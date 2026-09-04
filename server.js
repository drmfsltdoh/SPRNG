require("dotenv").config();
const express = require("express");
const cors = require("cors");
const bcrypt = require("bcrypt");
const jwt = require("jsonwebtoken");
const { MongoClient, ObjectId } = require("mongodb");
const crypto = require("crypto");

const app = express();
const PORT = process.env.PORT || 3001;

app.use(cors());
app.use(express.json());

// SECURITY: the Mongo URI now comes from .env — never hardcode credentials in code.
const uri = process.env.MONGODB_URI;
if (!uri) {
  console.error("Missing MONGODB_URI in .env — copy .env.example to .env and fill it in.");
  process.exit(1);
}
const client = new MongoClient(uri);

// ---------- Auth (JWT) ----------
// SECURITY: previously there was no session/token layer at all — every
// route just trusted whatever email/role showed up in the request body,
// and the admin routes had no gate whatsoever. This adds a real token
// layer: signup/login issue a JWT, and requireAuth/requireAdmin verify it.
//
// NOTE — this pass covers the admin routes (the ones flagged as unsafe to
// ship) end to end: they now hard-require a valid admin token. It does
// NOT yet migrate every rider/driver route off trusting req.body.email —
// that's a much bigger refactor touching most endpoints in this file, and
// isn't safe to do in the same pass without a way to test each one live.
// Treat that as the next hardening step, not something silently skipped.
const JWT_SECRET = process.env.JWT_SECRET;
if (!JWT_SECRET) {
  console.error("Missing JWT_SECRET in .env — copy .env.example to .env and fill it in.");
  process.exit(1);
}
const JWT_EXPIRY = "30d";

function signToken(user) {
  return jwt.sign(
    { userId: String(user._id), email: user.email, role: user.role },
    JWT_SECRET,
    { expiresIn: JWT_EXPIRY }
  );
}

function requireAuth(req, res, next) {
  const header = req.headers.authorization || "";
  const [scheme, token] = header.split(" ");
  if (scheme !== "Bearer" || !token) {
    return res.status(401).json({ error: "Missing or invalid Authorization header" });
  }
  try {
    req.user = jwt.verify(token, JWT_SECRET);
    next();
  } catch (e) {
    return res.status(401).json({ error: "Invalid or expired token" });
  }
}

function requireAdmin(req, res, next) {
  requireAuth(req, res, () => {
    if (req.user.role !== "admin") {
      return res.status(403).json({ error: "Admin access required" });
    }
    next();
  });
}

const VALID_CATEGORIES = ["economy", "comfort", "xl", "green"];

// ---------- Fare formula — SINGLE SOURCE OF TRUTH ----------
// This used to be hand-duplicated in mobile/src/utils/fare.js: change one
// number here, remember to change the matching number over there, or the
// two silently drift apart. That's fixed now — this backend is the only
// place these numbers live. The mobile app fetches them from
// GET /api/config/fare once at startup (see fetchFareConfig in
// mobile/src/context/AuthContext.js) and only falls back to its own
// bundled defaults if that fetch fails (e.g. fully offline first launch).
// To change pricing: edit the values below and redeploy the backend —
// nothing on the mobile side needs to change or be rebuilt.
const FUEL_PRICE_PER_LITER = 1500;
const AVERAGE_KM_PER_LITER = 10;
const MARKUP_MULTIPLIER = 2.5;
const BASE_FARE = 500;
const PLATFORM_FEE_RATE = 0.10; // Spring's cut of every completed fare
const PRICE_PER_KM = (FUEL_PRICE_PER_LITER / AVERAGE_KM_PER_LITER) * MARKUP_MULTIPLIER;
const FUEL_COST_PER_KM = FUEL_PRICE_PER_LITER / AVERAGE_KM_PER_LITER;
const CATEGORY_MULTIPLIERS = { economy: 1.0, comfort: 1.25, xl: 1.6, green: 0.9 };

const FARE_CONFIG = {
  FUEL_PRICE_PER_LITER,
  AVERAGE_KM_PER_LITER,
  MARKUP_MULTIPLIER,
  BASE_FARE,
  PLATFORM_FEE_RATE,
  CATEGORY_MULTIPLIERS,
};

function calculateFareForCategory(distanceKm, categoryId) {
  const base = BASE_FARE + Math.max(0, distanceKm || 0) * PRICE_PER_KM;
  const multiplier = CATEGORY_MULTIPLIERS[categoryId] ?? 1.0;
  return Math.round(base * multiplier);
}

// ---------- Locked-price matching queue ----------
// The rider still picks a specific driver up front (browse-and-pick stays
// the UX) — what changes is what happens when that driver doesn't answer.
// Instead of the ride just dying, the backend builds a fallback queue of
// the next-nearest same-category online drivers at request time and walks
// through it automatically on decline OR on timeout. The price is locked
// the moment estimatedFare is first stored below; escalating through the
// queue only ever swaps WHO is being asked, never re-quotes what they're
// asked to accept.
const MATCH_RESPONSE_TIMEOUT_MS = 20 * 1000; // 20s to accept/decline before auto-escalating
const MATCH_QUEUE_MAX_CANDIDATES = 5; // cap how many drivers get pinged per ride

async function buildMatchQueue(category, excludeDriverId, pickupLocation) {
  const candidates = await driversCollection
    .find({ online: true, vehicleType: category, _id: { $ne: excludeDriverId } })
    .toArray();
  const withDistance = candidates.map((d) => ({
    driverId: d._id,
    name: d.name,
    // Missing coords (either side) sort last, not excluded — a driver
    // shouldn't lose their spot in the queue just because location
    // tracking hasn't reported in yet.
    distanceMeters: pickupLocation && d.location ? distanceMetersBetween(pickupLocation, d.location) : null,
  }));
  withDistance.sort((a, b) => {
    if (a.distanceMeters == null && b.distanceMeters == null) return 0;
    if (a.distanceMeters == null) return 1;
    if (b.distanceMeters == null) return -1;
    return a.distanceMeters - b.distanceMeters;
  });
  return withDistance.slice(0, MATCH_QUEUE_MAX_CANDIDATES).map(({ driverId, name }) => ({ driverId, name }));
}

// Shared by the decline endpoint, the lazy timeout resolver, and the
// "driver went offline mid-match" hook — one place that knows how to move
// a ride to its next candidate (or give up) so all three stay consistent.
async function advanceMatchQueue(ride, outcome) {
  const now = new Date();
  const attempt = { driverId: ride.driverId, driverName: ride.driverName, outcome, respondedAt: now };
  const matchAttempts = [...(ride.matchAttempts || []), attempt];
  const queue = ride.matchQueue || [];

  let update;
  if (queue.length === 0) {
    update = { status: "unmatched", matchStatus: "exhausted", matchAttempts, unmatchedAt: now };
  } else {
    const [next, ...rest] = queue;
    update = {
      driverId: next.driverId,
      driverName: next.name,
      matchQueue: rest,
      matchAttempts,
      currentCandidateAssignedAt: now,
    };
  }
  await ridesCollection.updateOne({ _id: ride._id }, { $set: update });
  return { ...ride, ...update };
}

// Lazy — no job scheduler in this stack, so a stalled match is only
// noticed (and escalated) the next time the ride is read, same pattern as
// resolveExpiredDestinationChange below. Cheap: it's just a timestamp
// comparison unless the timeout has actually elapsed.
async function resolveStalledMatch(ride) {
  if (ride.status !== "requested" || ride.matchStatus !== "searching") return ride;
  if (!ride.currentCandidateAssignedAt) return ride;
  const elapsed = Date.now() - new Date(ride.currentCandidateAssignedAt).getTime();
  if (elapsed < MATCH_RESPONSE_TIMEOUT_MS) return ride;
  return advanceMatchQueue(ride, "timed_out");
}

// ---------- Route deviation protection ----------
// At trip start we ask Google Routes for the "optimal" route between
// pickup and destination and store its distance. At trip completion we
// compare that to what the driver's GPS actually logged. A trip is only
// flagged if it blows past BOTH a percentage tolerance and a minimum-km
// floor — the floor exists so a 2km trip that comes in at 2.3km (nothing
// but GPS drift and a couple of extra turns) never gets flagged just
// because 20% of a small number is an even smaller one.
const ROUTE_DEVIATION_TOLERANCE_PERCENT = 0.20; // 20% over the optimal route's distance
const ROUTE_DEVIATION_MIN_SLACK_KM = 1; // always allow at least 1km of slack
// Routes API is a sibling of Places API (New) on the same Google Cloud
// project — reuses GOOGLE_PLACES_API_KEY by default as long as "Routes
// API" is also enabled for it in Cloud Console; set GOOGLE_ROUTES_API_KEY
// separately only if you want a dedicated key/quota for it.
const ROUTES_KEY = process.env.GOOGLE_ROUTES_API_KEY || process.env.GOOGLE_PLACES_API_KEY;

// Never throws — missing key, missing coords, a bad API response, a
// network error all just resolve to null. A routing hiccup must never be
// able to block a trip from starting; "no optimal route on file" simply
// means no deviation protection for that one trip, same as today.
async function fetchOptimalRoute(origin, destination) {
  if (!ROUTES_KEY || !origin || !destination) return null;
  try {
    const googleRes = await fetch("https://routes.googleapis.com/directions/v2:computeRoutes", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "X-Goog-Api-Key": ROUTES_KEY,
        "X-Goog-FieldMask": "routes.distanceMeters,routes.duration",
      },
      body: JSON.stringify({
        origin: { location: { latLng: { latitude: origin.lat, longitude: origin.lng } } },
        destination: { location: { latLng: { latitude: destination.lat, longitude: destination.lng } } },
        travelMode: "DRIVE",
        routingPreference: "TRAFFIC_UNAWARE",
      }),
    });
    const data = await googleRes.json();
    if (!googleRes.ok || !data.routes?.[0]) {
      console.error("Routes API error:", data.error?.message || data);
      return null;
    }
    const route = data.routes[0];
    const durationSeconds = parseInt(route.duration, 10) || null; // Google returns e.g. "812s"
    return {
      distanceKm: route.distanceMeters / 1000,
      durationMinutes: durationSeconds ? Math.round(durationSeconds / 60) : null,
      calculatedAt: new Date(),
    };
  } catch (err) {
    console.error("Routes API request failed:", err.message);
    return null;
  }
}

// Decides what actually gets billed for a completed trip. No optimal
// route on file, or driven distance within tolerance -> bill exactly what
// was submitted (today's behavior, unchanged). Only a genuine deviation
// swaps in a capped fare and flags the ride for review.
function applyRouteDeviationProtection(ride, submittedDistanceKm, submittedFare, category) {
  const optimal = ride.optimalRoute;
  if (!optimal || typeof submittedDistanceKm !== "number") {
    return { fare: submittedFare, flagged: false, deviationKm: null, driverSubmittedFare: null };
  }
  const tolerance = Math.max(ROUTE_DEVIATION_MIN_SLACK_KM, optimal.distanceKm * ROUTE_DEVIATION_TOLERANCE_PERCENT);
  const capKm = optimal.distanceKm + tolerance;
  const deviationKm = Math.round((submittedDistanceKm - optimal.distanceKm) * 100) / 100;
  if (submittedDistanceKm <= capKm) {
    return { fare: submittedFare, flagged: false, deviationKm, driverSubmittedFare: null };
  }
  const cappedFare = calculateFareForCategory(capKm, category);
  const flaggedFare = typeof submittedFare === "number" ? Math.min(submittedFare, cappedFare) : cappedFare;
  return { fare: flaggedFare, flagged: true, deviationKm, driverSubmittedFare: submittedFare };
}

// ---------- Safety-first defaults ----------
// Three real, working pieces: an SOS button, an off-app-trip detector, and
// trip sharing. Emergency contacts live with the other profile routes
// further down. There's no push/SMS infrastructure in this stack, so
// "alerting someone" here means: land immediately in the admin's SLA-
// tracked support queue at "urgent" priority (reusing the ticket system
// built for #5) rather than inventing a second notification channel.
const OFF_APP_WARNING_MS = 3 * 60 * 1000;   // 3 min of driver-location silence -> soft in-app warning
const OFF_APP_INCIDENT_MS = 15 * 60 * 1000; // 15 min of silence -> auto safety incident + urgent ticket
const SOS_POST_TRIP_WINDOW_MS = 15 * 60 * 1000; // SOS still works up to 15 min after drop-off
const MAX_EMERGENCY_CONTACTS = 3;

// ---------- Transparent driver pay: logged-in/available time ----------
// The existing driver summary already showed exactly what a completed trip
// paid — this fills the real gap: Spring had NO record of a driver's
// online-but-not-on-a-trip time at all, so there was nothing to pay it
// from even if you wanted to. This adds that record (driverOnlineSessions)
// and a rate to pay it at.
//
// ⚠️ BUSINESS DECISION, NOT AN ENGINEERING ONE: ONLINE_TIME_PAY_PER_HOUR_NAIRA
// below is a placeholder so this feature is functional out of the box —
// it is NOT a researched or approved number. Set it to whatever Spring
// actually wants to guarantee per hour online (or 0, which effectively
// disables the payout while keeping the transparency — online hours would
// still show on the summary either way). The payout itself now uses the
// guaranteed-minimum model ("whichever is higher" — see /api/driver/:id/summary):
// a driver's day is never worth less than online hours × this rate; trip
// earnings only get topped up when they fall short of that floor, never a
// flat add-on on top of a day that already cleared it.
const ONLINE_TIME_PAY_PER_HOUR_NAIRA = 300;

// Sums how many minutes a driver was online within [since, now], clipping
// each session to that window (a session that started yesterday and is
// still open only counts from `since` forward; an open session counts up
// to right now).
async function onlineMinutesSince(driverId, since) {
  const now = new Date();
  const sessions = await driverOnlineSessionsCollection
    .find({ driverId, $or: [{ endedAt: null }, { endedAt: { $gte: since } }] })
    .toArray();
  let totalMs = 0;
  for (const s of sessions) {
    const start = new Date(Math.max(new Date(s.startedAt).getTime(), since.getTime()));
    const end = s.endedAt ? new Date(s.endedAt) : now;
    if (end > start) totalMs += end.getTime() - start.getTime();
  }
  return Math.round(totalMs / 60000);
}

// Shared by the SOS endpoint and the off-app auto-detector: writes the
// permanent incident record, then immediately opens an "urgent" support
// ticket against it (5 min first-response / 2 hr resolution SLA, per the
// SLA policy defined above) so it lands where support is already looking,
// with its own clock, without a separate alerting system.
async function logSafetyIncident({ ride, type, triggeredBy, location, note }) {
  const now = new Date();
  const incident = {
    rideId: ride._id,
    type, // "sos" | "off_app_suspected"
    triggeredBy, // "rider" | "driver" | "system"
    riderEmail: ride.riderEmail,
    driverId: ride.driverId || null,
    driverName: ride.driverName || null,
    location: location || null,
    note: note || null,
    status: "active", // active -> resolved
    createdAt: now,
    resolvedAt: null,
    resolutionNote: null,
  };
  const incidentResult = await safetyIncidentsCollection.insertOne(incident);

  let raisedByRole = "rider";
  let raisedByEmail = ride.riderEmail;
  let raisedByName = ride.riderName || null;
  if (triggeredBy === "driver" && ride.driverId) {
    const driver = await driversCollection.findOne({ _id: ride.driverId });
    if (driver) {
      raisedByRole = "driver";
      raisedByEmail = driver.email;
      raisedByName = driver.name;
    }
  }

  const priority = "urgent"; // safety always forces urgent — see CATEGORY_FORCED_PRIORITY
  const { firstResponseDueAt, resolutionDueAt } = slaDeadlines(priority, now);
  const description = note || (type === "sos"
    ? "Rider/driver triggered the SOS button mid-trip."
    : "No driver location update received for an extended period during an active trip.");
  const ticket = {
    raisedByRole,
    raisedByEmail,
    raisedByName,
    rideId: ride._id,
    category: "safety",
    priority,
    subject: type === "sos" ? "SOS triggered during a trip" : "Possible off-app trip detected",
    description,
    status: "open",
    assignedTo: null,
    firstRespondedAt: null,
    resolvedAt: null,
    closedAt: null,
    firstResponseDueAt,
    resolutionDueAt,
    createdAt: now,
    safetyIncidentId: incidentResult.insertedId,
  };
  const ticketResult = await supportTicketsCollection.insertOne(ticket);
  // Opening note comes from the system, not the reporter — it deliberately
  // does NOT set firstRespondedAt, since a human still has to actually
  // respond for that SLA clock to stop.
  await supportTicketMessagesCollection.insertOne({
    ticketId: ticketResult.insertedId,
    senderRole: "agent",
    senderName: "Spring Safety System",
    text: description,
    createdAt: now,
  });
  await safetyIncidentsCollection.updateOne(
    { _id: incidentResult.insertedId },
    { $set: { supportTicketId: ticketResult.insertedId } }
  );

  return { incidentId: incidentResult.insertedId, ticketId: ticketResult.insertedId };
}

// Lazy, batched — no job scheduler here either. Runs only against
// in_progress rides in whatever batch was just read, using ONE query for
// all their drivers' last-known-location timestamps rather than one per
// ride. A driver's app going quiet past OFF_APP_WARNING_MS decorates the
// ride so the rider's screen can show a soft warning; past
// OFF_APP_INCIDENT_MS it escalates to a real logged incident + ticket
// (only once per ride — offAppIncidentLogged guards against re-firing on
// every poll).
async function decorateOffAppRisk(rides) {
  const activeDriverIds = [...new Set(
    rides.filter((r) => r.status === "in_progress" && r.driverId).map((r) => r.driverId.toString())
  )];
  if (!activeDriverIds.length) return rides;

  const drivers = await driversCollection
    .find({ _id: { $in: activeDriverIds.map((id) => new ObjectId(id)) } })
    .toArray();
  const driverById = new Map(drivers.map((d) => [d._id.toString(), d]));
  const now = Date.now();

  return Promise.all(rides.map(async (ride) => {
    if (ride.status !== "in_progress" || !ride.driverId) return ride;
    const driver = driverById.get(ride.driverId.toString());
    const lastPing = driver?.locationUpdatedAt ? new Date(driver.locationUpdatedAt).getTime() : null;
    const silenceMs = lastPing != null ? now - lastPing : null;
    const decorated = {
      ...ride,
      offAppRisk: silenceMs != null && silenceMs > OFF_APP_WARNING_MS,
      driverLocationSilenceSeconds: silenceMs != null ? Math.round(silenceMs / 1000) : null,
    };
    if (silenceMs != null && silenceMs > OFF_APP_INCIDENT_MS && !ride.offAppIncidentLogged) {
      await logSafetyIncident({
        ride,
        type: "off_app_suspected",
        triggeredBy: "system",
        location: driver?.location || null,
        note: `No driver location update for ${Math.round(silenceMs / 60000)} minutes during an active trip — possible off-app continuation.`,
      });
      await ridesCollection.updateOne({ _id: ride._id }, { $set: { offAppIncidentLogged: true } });
      decorated.offAppIncidentLogged = true;
    }
    return decorated;
  }));
}

// ---------- Rider rating & appeals ----------
// Mirrors the driver-rating logic that already existed, in the other
// direction, plus a deactivation path that was entirely missing. Nobody
// gets deactivated off one bad ride: it takes a real sample size AND a
// meaningfully low average, and even then it's a 7-day WARNING
// (pending_deactivation), not an instant cutoff — the rider can keep
// riding, see the warning, and either improve or appeal before it becomes
// final. Recovering above threshold during that window cancels the
// warning automatically, same self-correcting spirit as the rest of this
// backend (auto-waived cancellation fees, auto-escalating matches).
const RIDER_DEACTIVATION_MIN_RATINGS = 5;
const RIDER_DEACTIVATION_THRESHOLD = 3.5;
const DEACTIVATION_APPEAL_WINDOW_MS = 7 * 24 * 60 * 60 * 1000; // 7 days to appeal before it's final

async function recalculateRiderRating(riderEmail) {
  const user = await usersCollection.findOne({ email: riderEmail });
  if (!user) return;

  const reviews = await reviewsCollection.find({ riderEmail, fromRole: "driver" }).toArray();
  const ratingCount = reviews.length;
  const avg = ratingCount ? reviews.reduce((sum, r) => sum + r.rating, 0) / ratingCount : null;
  const update = { rating: avg, ratingCount };

  const belowThreshold = avg != null && ratingCount >= RIDER_DEACTIVATION_MIN_RATINGS && avg < RIDER_DEACTIVATION_THRESHOLD;
  if (belowThreshold && (user.accountStatus || "active") === "active") {
    const now = new Date();
    update.accountStatus = "pending_deactivation";
    update.deactivationWarnedAt = now;
    update.deactivationDeadline = new Date(now.getTime() + DEACTIVATION_APPEAL_WINDOW_MS);
  } else if (!belowThreshold && user.accountStatus === "pending_deactivation") {
    update.accountStatus = "active";
    update.deactivationWarnedAt = null;
    update.deactivationDeadline = null;
  }

  await usersCollection.updateOne({ email: riderEmail }, { $set: update });
}

// Lazy — finalizes a pending deactivation once its 7-day window has
// passed, UNLESS an appeal is currently open against it (an unresolved
// appeal ticket pauses the clock, so it can never run out from under a
// rider who's actively being reviewed).
async function resolveRiderDeactivation(user) {
  if (!user || user.accountStatus !== "pending_deactivation") return user;
  if (!user.deactivationDeadline || new Date() < new Date(user.deactivationDeadline)) return user;

  if (user.appealTicketId) {
    const ticket = await supportTicketsCollection.findOne({ _id: user.appealTicketId });
    if (ticket && !["resolved", "closed"].includes(ticket.status)) return user;
  }

  await usersCollection.updateOne({ email: user.email }, { $set: { accountStatus: "deactivated" } });
  return { ...user, accountStatus: "deactivated" };
}

// Gate used by ride/package request creation — deactivated riders can't
// book new trips (they can still log in and see why, and file an appeal).
async function assertRiderNotDeactivated(riderEmail) {
  let riderUser = await usersCollection.findOne({ email: riderEmail, role: "rider" });
  if (!riderUser) return; // no rider account under this email — nothing to gate
  riderUser = await resolveRiderDeactivation(riderUser);
  if (riderUser.accountStatus === "deactivated") {
    throw badRequest("Your account has been deactivated due to low ratings. File an appeal from your Account screen to request a review.");
  }
}

// ---------- Fault-based cancellation fees ----------
// Trust feature: a rider should never be charged for a driver's no-show.
// CANCELLATION_FEE_NAIRA is a starting default — easy to tune or make
// category-dependent later. NO_SHOW_RADIUS_METERS is how close a driver
// must be to the pickup point for a rider-initiated cancellation to count
// as "the driver was there" (fee applies) vs "the driver never showed"
// (fee auto-waived, no support ticket needed).
const CANCELLATION_FEE_NAIRA = 500;
const NO_SHOW_RADIUS_METERS = 100;

// ---------- Destination-change consent gate ----------
// A driver can propose a new destination mid-trip, but it never takes
// effect silently — the rider must explicitly approve it first. If the
// rider doesn't respond in time, the change auto-fails safe: the ORIGINAL
// destination stays in effect, never the driver's proposed one.
const DESTINATION_CHANGE_TIMEOUT_MS = 30 * 1000; // 30s — a short, real window

// ---------- Support SLA tracker ----------
// Every ticket gets two clocks the moment it's created — a first-response
// deadline and a resolution deadline — set from its priority. There's no
// job scheduler in this stack (same constraint as the destination-change
// timeout above), so "breached" isn't a flag written by a cron job; it's
// computed live, on read, by comparing now() to the stored deadlines. That
// means the admin dashboard is never stale, and it costs nothing extra.
//
// Safety reports always get "urgent" no matter what category/priority the
// client sends — a rider/driver should never be able to (accidentally or
// otherwise) talk a safety report down to a slower queue.
const SLA_POLICY_MINUTES = {
  urgent: { firstResponse: 5, resolution: 120 },       // 5 min / 2 hrs — safety-adjacent
  high: { firstResponse: 30, resolution: 24 * 60 },    // 30 min / 24 hrs
  normal: { firstResponse: 4 * 60, resolution: 72 * 60 }, // 4 hrs / 72 hrs
};
const VALID_TICKET_CATEGORIES = [
  "safety", "cancellation_fee_dispute", "driver_behavior", "rider_behavior",
  "payment", "app_bug", "lost_item", "account_appeal", "other",
];
const CATEGORY_FORCED_PRIORITY = { safety: "urgent" };
const VALID_PRIORITIES = ["urgent", "high", "normal"];
const VALID_TICKET_STATUSES = ["open", "in_progress", "resolved", "closed"];

function derivePriority(category, requestedPriority) {
  if (CATEGORY_FORCED_PRIORITY[category]) return CATEGORY_FORCED_PRIORITY[category];
  if (requestedPriority && VALID_PRIORITIES.includes(requestedPriority)) return requestedPriority;
  return "normal";
}

function slaDeadlines(priority, createdAt) {
  const policy = SLA_POLICY_MINUTES[priority] || SLA_POLICY_MINUTES.normal;
  return {
    firstResponseDueAt: new Date(createdAt.getTime() + policy.firstResponse * 60000),
    resolutionDueAt: new Date(createdAt.getTime() + policy.resolution * 60000),
  };
}

// Attaches live SLA status to a ticket doc — never persisted, always
// recomputed against the current time. "Breached" only applies to clocks
// that are still running (an already-resolved ticket can't newly breach);
// "met" is the permanent record of whether each clock was hit, used for
// the compliance-rate stats on the admin summary.
function decorateTicketWithSla(ticket) {
  const now = new Date();
  const isOpenClock = !["resolved", "closed"].includes(ticket.status);
  const firstResponseBreached = isOpenClock && !ticket.firstRespondedAt && now > new Date(ticket.firstResponseDueAt);
  const resolutionBreached = isOpenClock && !ticket.resolvedAt && now > new Date(ticket.resolutionDueAt);
  const firstResponseMet = ticket.firstRespondedAt ? new Date(ticket.firstRespondedAt) <= new Date(ticket.firstResponseDueAt) : null;
  const resolutionMet = ticket.resolvedAt ? new Date(ticket.resolvedAt) <= new Date(ticket.resolutionDueAt) : null;
  return { ...ticket, firstResponseBreached, resolutionBreached, firstResponseMet, resolutionMet };
}

// Haversine distance in METERS — separate from the km version in the mobile
// app's fare.js since this runs in a different runtime with no shared code.
function distanceMetersBetween(a, b) {
  if (!a || !b || typeof a.lat !== "number" || typeof b.lat !== "number") return null;
  const R = 6371000;
  const dLat = ((b.lat - a.lat) * Math.PI) / 180;
  const dLng = ((b.lng - a.lng) * Math.PI) / 180;
  const lat1 = (a.lat * Math.PI) / 180;
  const lat2 = (b.lat * Math.PI) / 180;
  const h = Math.sin(dLat / 2) ** 2 + Math.cos(lat1) * Math.cos(lat2) * Math.sin(dLng / 2) ** 2;
  return R * 2 * Math.atan2(Math.sqrt(h), Math.sqrt(1 - h));
}

let ridesCollection;
let usersCollection;
let driversCollection;
let messagesCollection;
let reviewsCollection;
let walletsCollection;
let walletTransactionsCollection;
let cancellationsCollection;
let destinationChangesCollection;
let supportTicketsCollection;
let supportTicketMessagesCollection;
let safetyIncidentsCollection;
let driverOnlineSessionsCollection;

async function connectToDatabase() {
  await client.connect();
  const db = client.db("ridego");
  ridesCollection = db.collection("rides");
  usersCollection = db.collection("users");
  driversCollection = db.collection("drivers");
  messagesCollection = db.collection("messages");
  reviewsCollection = db.collection("reviews");
  walletsCollection = db.collection("wallets");
  walletTransactionsCollection = db.collection("walletTransactions");
  cancellationsCollection = db.collection("cancellations");
  destinationChangesCollection = db.collection("destinationChanges");
  supportTicketsCollection = db.collection("supportTickets");
  supportTicketMessagesCollection = db.collection("supportTicketMessages");
  safetyIncidentsCollection = db.collection("safetyIncidents");
  driverOnlineSessionsCollection = db.collection("driverOnlineSessions");

  // Keep signups unique and lookups fast. safe to run every boot — no-ops if they already exist.
  await usersCollection.createIndex({ email: 1 }, { unique: true });
  await driversCollection.createIndex({ email: 1 }, { unique: true });
  await ridesCollection.createIndex({ driverId: 1, createdAt: -1 });
  await ridesCollection.createIndex({ riderEmail: 1, createdAt: -1 });
  await ridesCollection.createIndex({ shareToken: 1 }, { sparse: true, unique: true });
  await messagesCollection.createIndex({ rideId: 1, createdAt: 1 });
  await walletsCollection.createIndex({ email: 1 }, { unique: true });
  await walletTransactionsCollection.createIndex({ email: 1, createdAt: -1 });
  await cancellationsCollection.createIndex({ rideId: 1 });
  await destinationChangesCollection.createIndex({ rideId: 1, requestedAt: -1 });
  // status+resolutionDueAt backs the admin triage queue (open/overdue first).
  await supportTicketsCollection.createIndex({ status: 1, resolutionDueAt: 1 });
  await supportTicketsCollection.createIndex({ raisedByRole: 1, raisedByEmail: 1, createdAt: -1 });
  await supportTicketMessagesCollection.createIndex({ ticketId: 1, createdAt: 1 });
  await safetyIncidentsCollection.createIndex({ status: 1, createdAt: -1 });
  await safetyIncidentsCollection.createIndex({ rideId: 1 });
  await driverOnlineSessionsCollection.createIndex({ driverId: 1, startedAt: -1 });

  console.log("Connected to MongoDB!");
}

connectToDatabase().catch((err) => {
  console.error("Failed to connect to MongoDB:", err.message);
  process.exit(1);
});

// ---------- helpers ----------

// Turns a route handler that returns a rejected promise (bad input, DB error,
// etc.) into a clean JSON error response instead of an unhandled rejection /
// a raw stack-trace dump to the client.
function asyncRoute(handler) {
  return (req, res, next) => Promise.resolve(handler(req, res, next)).catch(next);
}

// Guards every `new ObjectId(someParam)` call — previously a malformed id in
// the URL (e.g. a typo, or someone poking the API) threw synchronously
// inside an async function and the request would just hang with no
// response. Now it's a clean 400.
function toObjectId(id, label = "id") {
  if (!ObjectId.isValid(id)) {
    const err = new Error(`Invalid ${label}`);
    err.status = 400;
    throw err;
  }
  return new ObjectId(id);
}

function badRequest(message) {
  const err = new Error(message);
  err.status = 400;
  return err;
}

// If a driver's proposed destination change has sat unanswered past
// DESTINATION_CHANGE_TIMEOUT_MS, resolve it now as "expired" — the original
// destination silently wins, never the driver's proposed one. There's no
// job scheduler in this stack, so this runs lazily any time a ride is read
// (both apps poll every few seconds, so nothing waits long in practice).
async function resolveExpiredDestinationChange(ride) {
  const pending = ride.pendingDestinationChange;
  if (!pending || pending.status !== "pending") return ride;
  if (new Date() < new Date(pending.expiresAt)) return ride;

  const now = new Date();
  await ridesCollection.updateOne({ _id: ride._id }, { $set: { pendingDestinationChange: null } });
  await destinationChangesCollection.updateOne(
    { rideId: ride._id, requestedAt: pending.requestedAt },
    { $set: { outcome: "expired", resolvedAt: now } }
  );
  return { ...ride, pendingDestinationChange: null };
}

async function resolveExpiredDestinationChanges(rides) {
  return Promise.all(rides.map(resolveExpiredDestinationChange));
}

// Combined lazy-resolution pass for a ride read: expire any stale
// destination-change request, then check whether the current match
// candidate has gone quiet past MATCH_RESPONSE_TIMEOUT_MS and needs to be
// escalated. Order doesn't matter functionally (disjoint fields) — this
// just saves every read call site from having to know about both.
async function resolveRideState(ride) {
  const afterDestination = await resolveExpiredDestinationChange(ride);
  const afterMatch = await resolveStalledMatch(afterDestination);
  const [decorated] = await decorateOffAppRisk([afterMatch]);
  return decorated;
}

async function resolveRideStates(rides) {
  const afterDestination = await resolveExpiredDestinationChanges(rides);
  const afterMatch = await Promise.all(afterDestination.map(resolveStalledMatch));
  return decorateOffAppRisk(afterMatch);
}

app.get("/", (req, res) => {
  res.send("Spring backend is running!");
});

// Public — the mobile app fetches this once at startup so fare pricing
// only ever needs to be edited on the backend (see FARE_CONFIG above).
app.get("/api/config/fare", (req, res) => {
  res.json(FARE_CONFIG);
});

// ---------- AUTH ----------

app.post("/api/signup", asyncRoute(async (req, res) => {
  const { name, email, password, role, phone, car, plate, vehicleType, adminKey } = req.body;
  if (!name || !email || !password || !role) {
    throw badRequest("name, email, password and role are required");
  }
  // Admin accounts can't be self-service-created by just picking "admin" as
  // a role — that would defeat the whole point of gating the admin routes.
  // You create the first admin by signing up with role "admin" AND the
  // ADMIN_SIGNUP_KEY from your .env in the adminKey field (e.g. via a curl
  // request or Postman, not a public-facing screen). Rotate/remove that key
  // once you have the admin accounts you need.
  if (role === "admin") {
    if (!process.env.ADMIN_SIGNUP_KEY || adminKey !== process.env.ADMIN_SIGNUP_KEY) {
      throw badRequest("Invalid admin signup key");
    }
  } else if (!["rider", "driver"].includes(role)) {
    throw badRequest('role must be "rider" or "driver"');
  }
  if (password.length < 6) {
    throw badRequest("password must be at least 6 characters");
  }
  if (role === "driver" && vehicleType && !VALID_CATEGORIES.includes(vehicleType)) {
    throw badRequest(`vehicleType must be one of: ${VALID_CATEGORIES.join(", ")}`);
  }

  const normalizedEmail = email.trim().toLowerCase();
  const existingUser = await usersCollection.findOne({ email: normalizedEmail });
  if (existingUser) {
    throw badRequest("Email already registered");
  }

  const hashedPassword = await bcrypt.hash(password, 10);
  const newUser = {
    name: name.trim(),
    email: normalizedEmail,
    password: hashedPassword,
    role,
    phone: phone?.trim() || null,
    // Only meaningful for riders (rating & appeals) but harmless on drivers.
    accountStatus: "active",
    rating: null,
    ratingCount: 0,
  };
  const result = await usersCollection.insertOne(newUser);

  // Every rider (and driver) gets a Spring Wallet the moment they sign up,
  // starting at ₦0 — this is what backs the Payments → Spring Wallet screen.
  await walletsCollection.insertOne({ email: normalizedEmail, balance: 0, createdAt: new Date() });

  // If signing up as a driver, also create their driver profile
  let driverId;
  if (role === "driver") {
    const driverResult = await driversCollection.insertOne({
      userId: result.insertedId,
      name: name.trim(),
      email: normalizedEmail,
      car: car?.trim() || "Unknown vehicle",
      plate: plate?.trim() || "N/A",
      vehicleType: vehicleType || "economy", // economy | comfort | xl | green — which rider category this driver serves
      rating: 5.0,
      online: false,
      location: null, // { lat, lng }
    });
    driverId = driverResult.insertedId;
  }

  const token = signToken({ _id: result.insertedId, email: normalizedEmail, role });
  res.json({ message: "Signup successful!", token, name: newUser.name, email: normalizedEmail, phone: newUser.phone, role, driverId, vehicleType: role === "driver" ? (vehicleType || "economy") : undefined });
}));

app.post("/api/login", asyncRoute(async (req, res) => {
  const { email, password } = req.body;
  if (!email || !password) throw badRequest("email and password are required");

  const normalizedEmail = email.trim().toLowerCase();
  const user = await usersCollection.findOne({ email: normalizedEmail });
  if (!user) {
    return res.status(401).json({ error: "Invalid email or password" });
  }

  const passwordMatches = await bcrypt.compare(password, user.password);
  if (!passwordMatches) {
    return res.status(401).json({ error: "Invalid email or password" });
  }

  let driverId;
  let vehicleType;
  if (user.role === "driver") {
    const driverProfile = await driversCollection.findOne({ email: user.email });
    driverId = driverProfile?._id;
    vehicleType = driverProfile?.vehicleType;
  }

  // Backfill a wallet for accounts created before wallets existed.
  await walletsCollection.updateOne(
    { email: normalizedEmail },
    { $setOnInsert: { email: normalizedEmail, balance: 0, createdAt: new Date() } },
    { upsert: true }
  );

  const token = signToken(user);
  res.json({ message: "Login successful!", token, name: user.name, email: user.email, phone: user.phone || null, role: user.role, driverId, vehicleType });
}));

// Update name/phone from the Profile screen.
app.patch("/api/profile", asyncRoute(async (req, res) => {
  const { email, name, phone } = req.body;
  if (!email) throw badRequest("email is required");
  const update = {};
  if (typeof name === "string" && name.trim()) update.name = name.trim();
  if (typeof phone === "string") update.phone = phone.trim() || null;
  if (Object.keys(update).length === 0) throw badRequest("Nothing to update");

  const normalizedEmail = email.trim().toLowerCase();
  const result = await usersCollection.findOneAndUpdate(
    { email: normalizedEmail },
    { $set: update },
    { returnDocument: "after" }
  );
  if (!result) return res.status(404).json({ error: "User not found" });
  // Keep the driver profile's display name in sync too, if this user is a driver.
  if (update.name) {
    await driversCollection.updateOne({ email: normalizedEmail }, { $set: { name: update.name } });
  }
  res.json({ message: "Profile updated", name: result.name, phone: result.phone || null });
}));

// ---------- DRIVERS ----------

// Driver goes online/offline and updates live location
app.post("/api/driver/status", asyncRoute(async (req, res) => {
  const { email, online, location } = req.body;
  if (!email || typeof online !== "boolean") {
    throw badRequest("email and a boolean online are required");
  }
  if (location && (typeof location.lat !== "number" || typeof location.lng !== "number")) {
    throw badRequest("location must be { lat: number, lng: number }");
  }

  const driver = await driversCollection.findOne({ email: email.trim().toLowerCase() });
  if (!driver) return res.status(404).json({ error: "Driver not found" });

  await driversCollection.updateOne(
    { _id: driver._id },
    { $set: { online, ...(location ? { location, locationUpdatedAt: new Date() } : {}) } }
  );

  // Online-time pay tracking: open a session the moment they go online,
  // close it the moment they go offline. Only acts on an actual
  // transition (comparing against driver.online as read BEFORE this
  // update) so repeated "online: true" pings from the same app session
  // don't open a new session every time.
  const now = new Date();
  if (online === true && !driver.online) {
    await driverOnlineSessionsCollection.insertOne({ driverId: driver._id, startedAt: now, endedAt: null });
  }
  if (online === false && driver.online) {
    const openSession = await driverOnlineSessionsCollection.findOne({ driverId: driver._id, endedAt: null });
    if (openSession) {
      await driverOnlineSessionsCollection.updateOne(
        { _id: openSession._id },
        { $set: { endedAt: now, durationMinutes: Math.round((now - new Date(openSession.startedAt)) / 60000) } }
      );
    }
  }

  // Going offline mid-match shouldn't leave a rider silently waiting out
  // the full MATCH_RESPONSE_TIMEOUT_MS on a driver who just logged off —
  // escalate any ride currently pinged to them right away instead.
  if (online === false) {
    const strandedRides = await ridesCollection
      .find({ driverId: driver._id, status: "requested", matchStatus: "searching" })
      .toArray();
    for (const ride of strandedRides) {
      await advanceMatchQueue(ride, "driver_went_offline");
    }
  }

  res.json({ message: "Driver status updated" });
}));

// Rider-facing: list of currently online/available drivers
app.get("/api/drivers/available", asyncRoute(async (req, res) => {
  const drivers = await driversCollection.find({ online: true }).toArray();
  res.json(drivers);
}));

// Rider-facing: fetch one driver's current info + live location (used for real-time tracking)
app.get("/api/driver/:id", asyncRoute(async (req, res) => {
  const driver = await driversCollection.findOne({ _id: toObjectId(req.params.id, "driver id") });
  if (!driver) return res.status(404).json({ error: "Driver not found" });
  res.json(driver);
}));

// ---------- RIDES ----------

// Rider requests a SPECIFIC driver (browse-and-pick flow)
app.post("/api/rides/request", asyncRoute(async (req, res) => {
  const { riderEmail, riderName, driverId, pickup, destination, pickupLocation, destinationLocation, category, estimatedFare } = req.body;
  if (!riderEmail || !driverId || !pickup?.trim() || !destination?.trim()) {
    throw badRequest("riderEmail, driverId, pickup and destination are required");
  }
  if (category && !VALID_CATEGORIES.includes(category)) {
    throw badRequest(`category must be one of: ${VALID_CATEGORIES.join(", ")}`);
  }
  await assertRiderNotDeactivated(riderEmail.trim().toLowerCase());

  const driver = await driversCollection.findOne({ _id: toObjectId(driverId, "driver id") });
  if (!driver || !driver.online) {
    throw badRequest("That driver is no longer available");
  }

  const now = new Date();
  const rideCategory = category || "economy";
  const rideePickupLocation = pickupLocation && typeof pickupLocation.lat === "number" ? pickupLocation : null;
  // The rest of the same-category online fleet, nearest-first, minus the
  // driver the rider actually picked — this is the fallback list decline/
  // timeout walks through automatically. Built once, up front, so the
  // locked price never has a reason to be re-quoted mid-search.
  const matchQueue = await buildMatchQueue(rideCategory, driver._id, rideePickupLocation);

  const newRide = {
    riderEmail: riderEmail.trim().toLowerCase(),
    riderName,
    driverId: driver._id,
    driverName: driver.name,
    pickup: pickup.trim(),
    destination: destination.trim(),
    // Coordinates alongside the display strings above — needed for
    // fault-based cancellation fees (was the driver actually near pickup?)
    // and for route-deviation checks later. Optional so older clients
    // that haven't sent them yet don't 400.
    pickupLocation: rideePickupLocation,
    destinationLocation: destinationLocation && typeof destinationLocation.lat === "number" ? destinationLocation : null,
    category: rideCategory,
    estimatedFare: typeof estimatedFare === "number" ? Math.round(estimatedFare) : null,
    status: "requested", // requested -> accepted -> in_progress -> completed | declined | cancelled | unmatched
    // matchStatus: "searching" while auto-escalating through candidates,
    // "locked" once someone accepts, "exhausted" if the whole queue says no.
    matchStatus: "searching",
    matchQueue,
    matchAttempts: [],
    currentCandidateAssignedAt: now,
    optimalRoute: null, // filled in once the trip actually starts (route deviation protection)
    distanceKm: null, // filled in once the trip completes
    fare: null,        // filled in once the trip completes
    createdAt: now,
  };
  const result = await ridesCollection.insertOne(newRide);
  res.json({ message: "Ride requested!", id: result.insertedId, ride: { ...newRide, _id: result.insertedId } });
}));

// Driver portal: see incoming requests addressed to them
app.get("/api/rides/driver/:driverId", asyncRoute(async (req, res) => {
  const rides = await ridesCollection
    .find({ driverId: toObjectId(req.params.driverId, "driver id") })
    .sort({ createdAt: -1 })
    .toArray();
  res.json(await resolveRideStates(rides));
}));

// Rider: see their own ride history / current ride status
app.get("/api/rides/rider/:riderEmail", asyncRoute(async (req, res) => {
  const rides = await ridesCollection
    .find({ riderEmail: req.params.riderEmail.trim().toLowerCase() })
    .sort({ createdAt: -1 })
    .toArray();
  res.json(await resolveRideStates(rides));
}));

// Single ride lookup — used for polling a specific trip (e.g. a driver
// waiting to hear back on a destination-change request) without pulling
// the rider's/driver's whole ride history.
app.get("/api/rides/:id", asyncRoute(async (req, res) => {
  const ride = await ridesCollection.findOne({ _id: toObjectId(req.params.id) });
  if (!ride) return res.status(404).json({ error: "Ride not found" });
  res.json(await resolveRideState(ride));
}));

// Driver accepts a ride request. Requires the accepting driverId to match
// whoever the ride is CURRENTLY pinged to — without this, a driver whose
// stale app still shows an old "Accept" button (after they declined, timed
// out, or the rider's request already moved on) could hijack a ride that
// isn't theirs anymore.
app.post("/api/rides/:id/accept", asyncRoute(async (req, res) => {
  const { driverId } = req.body;
  const rideId = toObjectId(req.params.id);
  const ride = await ridesCollection.findOne({ _id: rideId, status: "requested" });
  if (!ride) return res.status(409).json({ error: "Ride is no longer pending (already accepted/declined)" });
  if (driverId && ride.driverId?.toString() !== driverId) {
    return res.status(409).json({ error: "This ride has already moved on to another driver" });
  }

  await ridesCollection.updateOne({ _id: rideId }, { $set: { status: "accepted", matchStatus: "locked" } });
  res.json({ message: "Ride accepted" });
}));

// Driver declines a ride request — automatically escalates to the next
// nearest driver in the match queue instead of just dying (see
// advanceMatchQueue above). Same stale-app guard as accept.
app.post("/api/rides/:id/decline", asyncRoute(async (req, res) => {
  const { driverId } = req.body;
  const rideId = toObjectId(req.params.id);
  const ride = await ridesCollection.findOne({ _id: rideId, status: "requested" });
  if (!ride) return res.status(409).json({ error: "Ride is no longer pending" });
  if (driverId && ride.driverId?.toString() !== driverId) {
    return res.status(409).json({ error: "This ride has already moved on to another driver" });
  }

  const updated = await advanceMatchQueue(ride, "declined");
  const message = updated.status === "unmatched"
    ? "Ride declined — no more nearby drivers to offer it to"
    : "Ride declined — automatically offered to the next nearest driver";
  res.json({ message, status: updated.status, matchStatus: updated.matchStatus });
}));

// Either party marks the trip in progress / completed.
//
// in_progress: kicks off route-deviation protection by asking Google
// Routes for the optimal pickup->destination route and storing its
// distance — nothing to compare actual distance against later without it.
//
// completed: the client (driver app, which tracks the live GPS distance)
// passes distanceKm + fare so the final price is saved on the ride.
// applyRouteDeviationProtection compares the driven distance against the
// optimal route captured at trip start; only a genuine deviation swaps in
// a capped fare and flags the ride — otherwise the submitted fare is
// billed exactly as before.
app.post("/api/rides/:id/status", asyncRoute(async (req, res) => {
  const { status, distanceKm, fare } = req.body; // "in_progress" | "completed"
  if (!["in_progress", "completed"].includes(status)) {
    throw badRequest('status must be "in_progress" or "completed"');
  }

  const rideId = toObjectId(req.params.id);
  const ride = await ridesCollection.findOne({ _id: rideId });
  if (!ride) return res.status(404).json({ error: "Ride not found" });

  const update = { status };

  if (status === "in_progress" && !ride.optimalRoute) {
    const optimalRoute = await fetchOptimalRoute(ride.pickupLocation, ride.destinationLocation);
    if (optimalRoute) update.optimalRoute = optimalRoute;
  }

  let flaggedForReview = false;
  if (status === "completed") {
    update.completedAt = new Date();
    const submittedDistanceKm = typeof distanceKm === "number" ? Math.max(0, distanceKm) : null;
    const submittedFare = typeof fare === "number" ? Math.max(0, Math.round(fare)) : null;
    if (submittedDistanceKm !== null) update.distanceKm = submittedDistanceKm;

    const protection = applyRouteDeviationProtection(ride, submittedDistanceKm, submittedFare, ride.category);
    if (submittedFare !== null || protection.flagged) update.fare = protection.fare;
    if (protection.deviationKm !== null) {
      update.routeDeviation = {
        flagged: protection.flagged,
        deviationKm: protection.deviationKm,
        driverSubmittedFare: protection.driverSubmittedFare,
      };
      flaggedForReview = protection.flagged;
    }
  }

  await ridesCollection.updateOne({ _id: rideId }, { $set: update });
  const response = { message: `Ride marked as ${status}` };
  if (flaggedForReview) {
    response.routeDeviationFlagged = true;
    response.note = "Trip distance came in well above the optimal route — fare was capped for the rider and flagged for review.";
  }
  res.json(response);
}));

// Cancel a ride/package before it's underway, with fault-based fee logic:
//
//  - Cancelling before any driver has accepted ("requested") never incurs a
//    fee — nothing was promised yet.
//  - Cancelling after a driver accepted DOES risk a fee, but ONLY if the
//    driver was actually near the pickup point (within NO_SHOW_RADIUS_METERS)
//    at the moment of cancellation. If the driver's last known location is
//    farther than that (or missing entirely), the fee is auto-waived — no
//    support ticket needed, no back-and-forth. This is the whole point:
//    riders should never be charged for a driver's no-show.
//  - A driver-initiated cancellation never charges the rider a fee.
//
// Every cancellation — fee or no fee — is written to `cancellations` as a
// timestamped audit record (both parties' GPS, computed distance, and the
// reasoning) so a dispute can be resolved by looking at data instead of
// he-said-she-said.
app.post("/api/rides/:id/cancel", asyncRoute(async (req, res) => {
  const { cancelledBy, location } = req.body; // cancelledBy: "rider" | "driver"; location: canceller's own current { lat, lng }
  if (!["rider", "driver"].includes(cancelledBy)) {
    throw badRequest('cancelledBy must be "rider" or "driver"');
  }
  if (location && (typeof location.lat !== "number" || typeof location.lng !== "number")) {
    throw badRequest("location must be { lat: number, lng: number }");
  }

  const rideId = toObjectId(req.params.id);
  const ride = await ridesCollection.findOne({ _id: rideId });
  if (!ride) return res.status(404).json({ error: "Ride not found" });
  if (!["requested", "accepted"].includes(ride.status)) {
    return res.status(409).json({ error: `Can't cancel a ride that is already ${ride.status}` });
  }

  // The driver's location at the moment of cancellation: if the driver is
  // the one cancelling, trust the fresh GPS point they just sent; otherwise
  // (rider cancelling) fall back to the driver's last known live location.
  let driverLocation = null;
  if (cancelledBy === "driver") {
    driverLocation = location || null;
  } else {
    const driver = await driversCollection.findOne({ _id: ride.driverId });
    driverLocation = driver?.location || null;
  }
  const riderLocation = cancelledBy === "rider" ? location || null : null;

  const distanceMeters = distanceMetersBetween(driverLocation, ride.pickupLocation);

  let feeCharged = false;
  let reason;
  if (cancelledBy === "driver") {
    reason = "Driver-initiated cancellation — riders are never charged when the driver cancels.";
  } else if (ride.status === "requested") {
    reason = "No driver had accepted yet — nothing to charge for.";
  } else if (distanceMeters == null) {
    reason = "Driver's location wasn't available to verify — fee auto-waived in the rider's favor.";
  } else if (distanceMeters <= NO_SHOW_RADIUS_METERS) {
    feeCharged = true;
    reason = `Driver was already at the pickup point (${Math.round(distanceMeters)}m away) when you cancelled.`;
  } else {
    reason = `Driver was still ${Math.round(distanceMeters)}m from the pickup point — this looked like a no-show, so the fee was automatically waived.`;
  }

  const feeAmount = feeCharged ? CANCELLATION_FEE_NAIRA : 0;
  const now = new Date();

  await ridesCollection.updateOne(
    { _id: rideId },
    { $set: { status: "cancelled", cancelledBy, cancelledAt: now, cancellationFee: feeAmount } }
  );

  if (feeCharged) {
    // Debit the rider (in-house wallet ledger — can go negative, same as
    // any other simple ledger; there's no card auto-charge wired up yet).
    await walletsCollection.updateOne(
      { email: ride.riderEmail },
      { $setOnInsert: { email: ride.riderEmail, createdAt: now }, $inc: { balance: -feeAmount } },
      { upsert: true }
    );
    await walletTransactionsCollection.insertOne({
      email: ride.riderEmail,
      type: "cancellation_fee",
      amount: -feeAmount,
      note: `Cancellation fee — driver was at the pickup point (ride ${rideId})`,
      rideId,
      createdAt: now,
    });
    // Compensate the driver for the wasted trip to pickup.
    if (ride.driverId) {
      const driver = await driversCollection.findOne({ _id: ride.driverId });
      if (driver?.email) {
        await walletsCollection.updateOne(
          { email: driver.email },
          { $setOnInsert: { email: driver.email, createdAt: now }, $inc: { balance: feeAmount } },
          { upsert: true }
        );
        await walletTransactionsCollection.insertOne({
          email: driver.email,
          type: "cancellation_compensation",
          amount: feeAmount,
          note: `No-show compensation — rider cancelled after you reached pickup (ride ${rideId})`,
          rideId,
          createdAt: now,
        });
      }
    }
  }

  await cancellationsCollection.insertOne({
    rideId,
    cancelledBy,
    riderLocation,
    driverLocation,
    pickupLocation: ride.pickupLocation || null,
    distanceMeters,
    feeCharged,
    feeAmount,
    reason,
    createdAt: now,
  });

  res.json({ message: "Ride cancelled", feeCharged, feeAmount, distanceMeters, reason });
}));

// Driver proposes a new destination mid-trip. This does NOT change the
// ride's destination yet — it only stores a pending proposal and starts the
// clock. The rider must explicitly approve via /destination-change/respond
// before anything changes; if the window lapses, resolveExpiredDestinationChange
// (run lazily whenever the ride is next read) fails it safe to the original
// destination.
app.post("/api/rides/:id/destination-change/request", asyncRoute(async (req, res) => {
  const { newDestination, newDestinationLocation } = req.body;
  if (!newDestination?.trim()) throw badRequest("newDestination is required");
  if (!newDestinationLocation || typeof newDestinationLocation.lat !== "number") {
    throw badRequest("newDestinationLocation must be { lat: number, lng: number }");
  }

  const rideId = toObjectId(req.params.id);
  const ride = await ridesCollection.findOne({ _id: rideId });
  if (!ride) return res.status(404).json({ error: "Ride not found" });
  if (!["accepted", "in_progress"].includes(ride.status)) {
    throw badRequest("Can only propose a destination change on an active trip");
  }
  if (ride.pendingDestinationChange?.status === "pending") {
    throw badRequest("There is already a destination change waiting on the rider's response");
  }

  const now = new Date();
  const pending = {
    newDestination: newDestination.trim(),
    newDestinationLocation,
    previousDestination: ride.destination,
    previousDestinationLocation: ride.destinationLocation || null,
    requestedAt: now,
    expiresAt: new Date(now.getTime() + DESTINATION_CHANGE_TIMEOUT_MS),
    status: "pending",
  };

  await ridesCollection.updateOne({ _id: rideId }, { $set: { pendingDestinationChange: pending } });
  await destinationChangesCollection.insertOne({
    rideId,
    requestedBy: "driver",
    newDestination: pending.newDestination,
    newDestinationLocation,
    previousDestination: pending.previousDestination,
    previousDestinationLocation: pending.previousDestinationLocation,
    requestedAt: now,
    outcome: "pending",
    resolvedAt: null,
  });

  res.json({ message: "Destination change proposed — waiting on rider approval", pendingDestinationChange: pending });
}));

// Rider approves or rejects a pending destination change.
app.post("/api/rides/:id/destination-change/respond", asyncRoute(async (req, res) => {
  const { approve } = req.body;
  if (typeof approve !== "boolean") throw badRequest("approve must be a boolean");

  const rideId = toObjectId(req.params.id);
  const ride = await ridesCollection.findOne({ _id: rideId });
  if (!ride) return res.status(404).json({ error: "Ride not found" });

  const pending = ride.pendingDestinationChange;
  if (!pending || pending.status !== "pending") {
    return res.status(409).json({ error: "No destination change is waiting on a response" });
  }
  if (new Date() >= new Date(pending.expiresAt)) {
    // Already timed out — let the lazy-expiry path handle it consistently.
    await resolveExpiredDestinationChange(ride);
    return res.status(409).json({ error: "This destination change request has expired" });
  }

  const now = new Date();
  const update = { pendingDestinationChange: null };
  if (approve) {
    update.destination = pending.newDestination;
    update.destinationLocation = pending.newDestinationLocation;
    // The optimal route calculated at trip start was for the OLD
    // destination — comparing actual distance against it after a genuine
    // destination change would unfairly flag the driver. Recompute against
    // the new endpoint (fails open, same as the trip-start call, so this
    // never blocks the approval itself).
    if (ride.optimalRoute && ride.pickupLocation) {
      const recomputed = await fetchOptimalRoute(ride.pickupLocation, pending.newDestinationLocation);
      if (recomputed) update.optimalRoute = recomputed;
    }
  }
  await ridesCollection.updateOne({ _id: rideId }, { $set: update });
  await destinationChangesCollection.updateOne(
    { rideId, requestedAt: pending.requestedAt },
    { $set: { outcome: approve ? "approved" : "rejected", resolvedAt: now } }
  );

  res.json({
    message: approve ? "Destination change approved" : "Destination change rejected",
    destination: approve ? pending.newDestination : ride.destination,
  });
}));

// ---------- SAFETY-FIRST DEFAULTS (routes) ----------

// Either party hits SOS mid-trip (or shortly after drop-off). Logs a
// permanent incident and immediately opens an urgent, SLA-tracked support
// ticket — see logSafetyIncident above for why that's the whole alerting
// mechanism here (no separate push/SMS system exists).
app.post("/api/rides/:id/sos", asyncRoute(async (req, res) => {
  const { triggeredBy, location } = req.body; // "rider" | "driver"
  if (!["rider", "driver"].includes(triggeredBy)) {
    throw badRequest('triggeredBy must be "rider" or "driver"');
  }
  if (location && (typeof location.lat !== "number" || typeof location.lng !== "number")) {
    throw badRequest("location must be { lat: number, lng: number }");
  }

  const ride = await ridesCollection.findOne({ _id: toObjectId(req.params.id) });
  if (!ride) return res.status(404).json({ error: "Ride not found" });

  const isActive = ["accepted", "in_progress"].includes(ride.status);
  const isRecentlyCompleted = ride.status === "completed" && ride.completedAt
    && Date.now() - new Date(ride.completedAt).getTime() < SOS_POST_TRIP_WINDOW_MS;
  if (!isActive && !isRecentlyCompleted) {
    throw badRequest("SOS can only be triggered during an active trip, or shortly after it ends");
  }

  const { incidentId, ticketId } = await logSafetyIncident({
    ride,
    type: "sos",
    triggeredBy,
    location: location || null,
    note: `${triggeredBy === "rider" ? "Rider" : "Driver"} triggered SOS during ride ${ride._id}.`,
  });

  await ridesCollection.updateOne(
    { _id: ride._id },
    { $set: { sos: { triggeredBy, at: new Date(), location: location || null, incidentId } } }
  );

  res.json({ message: "SOS received — this has been flagged for urgent review", incidentId, ticketId });
}));

// Generates (or returns the existing) shareable trip link — a rider can
// send this to someone outside the app to track the trip live, no login
// required on their end.
app.post("/api/rides/:id/share", asyncRoute(async (req, res) => {
  const rideId = toObjectId(req.params.id);
  const ride = await ridesCollection.findOne({ _id: rideId });
  if (!ride) return res.status(404).json({ error: "Ride not found" });
  if (ride.shareToken) return res.json({ shareToken: ride.shareToken });

  const shareToken = crypto.randomBytes(12).toString("hex");
  await ridesCollection.updateOne({ _id: rideId }, { $set: { shareToken } });
  res.json({ shareToken });
}));

// Public, unauthenticated — the whole point is someone without the app can
// open this. Returns ONLY a safety-relevant subset: never rider/driver
// email or phone, never the fare, live location only while the trip is
// actually under way.
app.get("/api/share/:token", asyncRoute(async (req, res) => {
  const ride = await ridesCollection.findOne({ shareToken: req.params.token });
  if (!ride) return res.status(404).json({ error: "This trip link is invalid or has expired" });

  let driverLocation = null;
  let driverRating = null;
  let vehicle = null;
  if (ride.driverId) {
    const driver = await driversCollection.findOne({ _id: ride.driverId });
    if (driver) {
      driverRating = driver.rating ?? null;
      vehicle = { car: driver.car, plate: driver.plate, vehicleType: driver.vehicleType };
      if (["accepted", "in_progress"].includes(ride.status)) driverLocation = driver.location || null;
    }
  }

  res.json({
    status: ride.status,
    pickup: ride.pickup,
    destination: ride.destination,
    riderFirstName: (ride.riderName || "").trim().split(" ")[0] || "Rider",
    driverName: ride.driverName || null,
    driverRating,
    vehicle,
    driverLocation,
    createdAt: ride.createdAt,
    completedAt: ride.completedAt || null,
  });
}));

// Set/replace the caller's emergency contacts (used by SOS follow-up and
// shown on the rider/driver Safety screen). Full replace, capped at 3 —
// simpler and safer than incremental add/remove for a list this short.
app.put("/api/profile/emergency-contacts", asyncRoute(async (req, res) => {
  const { email, contacts } = req.body;
  if (!email) throw badRequest("email is required");
  if (!Array.isArray(contacts)) throw badRequest("contacts must be an array");
  if (contacts.length > MAX_EMERGENCY_CONTACTS) {
    throw badRequest(`You can save up to ${MAX_EMERGENCY_CONTACTS} emergency contacts`);
  }
  const cleaned = contacts.map((c, i) => {
    if (!c?.name?.trim() || !c?.phone?.trim()) {
      throw badRequest(`Contact ${i + 1} needs both a name and a phone number`);
    }
    return { name: c.name.trim().slice(0, 100), phone: c.phone.trim().slice(0, 30) };
  });

  const normalizedEmail = email.trim().toLowerCase();
  const result = await usersCollection.findOneAndUpdate(
    { email: normalizedEmail },
    { $set: { emergencyContacts: cleaned } },
    { returnDocument: "after" }
  );
  if (!result) return res.status(404).json({ error: "User not found" });
  res.json({ message: "Emergency contacts updated", emergencyContacts: cleaned });
}));

app.get("/api/profile/emergency-contacts/:email", asyncRoute(async (req, res) => {
  const user = await usersCollection.findOne({ email: req.params.email.trim().toLowerCase() });
  if (!user) return res.status(404).json({ error: "User not found" });
  res.json({ emergencyContacts: user.emergencyContacts || [] });
}));

// Admin: safety incident queue (SOS + auto-detected off-app trips).
app.get("/api/admin/safety/incidents", requireAdmin, asyncRoute(async (req, res) => {
  const { status } = req.query;
  const query = {};
  if (status) {
    if (!["active", "resolved"].includes(status)) throw badRequest("invalid status filter");
    query.status = status;
  }
  const incidents = await safetyIncidentsCollection.find(query).sort({ createdAt: -1 }).limit(200).toArray();
  res.json(incidents);
}));

app.post("/api/admin/safety/incidents/:id/resolve", requireAdmin, asyncRoute(async (req, res) => {
  const { resolutionNote } = req.body;
  const incidentId = toObjectId(req.params.id, "incident id");
  const result = await safetyIncidentsCollection.updateOne(
    { _id: incidentId },
    { $set: { status: "resolved", resolvedAt: new Date(), resolutionNote: resolutionNote?.trim() || null } }
  );
  if (result.matchedCount === 0) return res.status(404).json({ error: "Incident not found" });
  res.json({ message: "Incident marked resolved" });
}));

// ---------- MESSAGES (rider <-> driver chat, scoped to one ride) ----------

// Send a message on a ride's chat thread
app.post("/api/rides/:id/messages", asyncRoute(async (req, res) => {
  const { senderRole, senderName, text } = req.body; // senderRole: "rider" | "driver"
  if (!senderRole || !text?.trim()) {
    throw badRequest("senderRole and text are required");
  }
  const message = {
    rideId: toObjectId(req.params.id),
    senderRole,
    senderName,
    text: text.trim().slice(0, 2000),
    createdAt: new Date(),
  };
  const result = await messagesCollection.insertOne(message);
  res.json({ message: "Sent", data: { ...message, _id: result.insertedId } });
}));

// Fetch all messages for a ride's chat thread, oldest first
app.get("/api/rides/:id/messages", asyncRoute(async (req, res) => {
  const messages = await messagesCollection
    .find({ rideId: toObjectId(req.params.id) })
    .sort({ createdAt: 1 })
    .toArray();
  res.json(messages);
}));

// One row per ride/package that ever reached a chat-capable stage (a driver
// was actually matched), each with a preview of its most recent message —
// this is what backs the Communication → Messages inbox screen.
app.get("/api/inbox/:role/:id", asyncRoute(async (req, res) => {
  const { role, id } = req.params;
  if (!["rider", "driver"].includes(role)) throw badRequest('role must be "rider" or "driver"');

  const rides = role === "rider"
    ? await ridesCollection.find({ riderEmail: id.trim().toLowerCase() }).sort({ createdAt: -1 }).toArray()
    : await ridesCollection.find({ driverId: toObjectId(id, "driver id") }).sort({ createdAt: -1 }).toArray();

  const chattable = rides.filter((r) => ["accepted", "in_progress", "completed"].includes(r.status));
  if (chattable.length === 0) return res.json([]);

  const rideIds = chattable.map((r) => r._id);
  const lastMessages = await messagesCollection.aggregate([
    { $match: { rideId: { $in: rideIds } } },
    { $sort: { createdAt: -1 } },
    { $group: { _id: "$rideId", text: { $first: "$text" }, senderRole: { $first: "$senderRole" }, createdAt: { $first: "$createdAt" } } },
  ]).toArray();
  const lastMessageByRide = Object.fromEntries(
    lastMessages.map((m) => [m._id.toString(), { text: m.text, senderRole: m.senderRole, createdAt: m.createdAt }])
  );

  res.json(chattable.map((r) => ({
    rideId: r._id,
    otherPartyName: role === "rider" ? r.driverName : r.riderName,
    pickup: r.pickup,
    destination: r.destination,
    status: r.status,
    type: r.type || "ride",
    lastMessage: lastMessageByRide[r._id.toString()] || null,
  })));
}));

// ---------- REVIEWS ----------

// Rider AND driver each leave a review after a completed ride — this now
// genuinely flows both ways. One review per (ride, fromRole): a second
// attempt is rejected rather than silently averaged in again.
app.post("/api/rides/:id/review", asyncRoute(async (req, res) => {
  const { fromRole, rating, comment } = req.body; // fromRole: "rider" | "driver"
  if (!fromRole || !rating) {
    throw badRequest("fromRole and rating are required");
  }
  if (!["rider", "driver"].includes(fromRole)) {
    throw badRequest('fromRole must be "rider" or "driver"');
  }
  if (typeof rating !== "number" || rating < 1 || rating > 5) {
    throw badRequest("rating must be a number between 1 and 5");
  }

  const ride = await ridesCollection.findOne({ _id: toObjectId(req.params.id) });
  if (!ride) return res.status(404).json({ error: "Ride not found" });

  const existing = await reviewsCollection.findOne({ rideId: ride._id, fromRole });
  if (existing) return res.status(409).json({ error: "You've already left a review for this ride" });

  const review = {
    rideId: ride._id,
    driverId: ride.driverId,
    riderEmail: ride.riderEmail,
    fromRole,
    rating,
    comment: comment?.trim().slice(0, 1000) || "",
    createdAt: new Date(),
  };
  await reviewsCollection.insertOne(review);

  // Rider rated the driver -> recalculate the driver's average (unchanged
  // from before). Driver rated the rider -> recalculate the RIDER's
  // average, which is the new half — see recalculateRiderRating above for
  // the deactivation-warning logic that rides on top of this.
  if (fromRole === "rider" && ride.driverId) {
    const driverReviews = await reviewsCollection.find({ driverId: ride.driverId, fromRole: "rider" }).toArray();
    const avg = driverReviews.reduce((sum, r) => sum + r.rating, 0) / driverReviews.length;
    await driversCollection.updateOne({ _id: ride.driverId }, { $set: { rating: avg } });
  }
  if (fromRole === "driver" && ride.riderEmail) {
    await recalculateRiderRating(ride.riderEmail);
  }

  res.json({ message: "Review submitted" });
}));

// Get all reviews for a specific driver
app.get("/api/driver/:id/reviews", asyncRoute(async (req, res) => {
  const reviews = await reviewsCollection
    .find({ driverId: toObjectId(req.params.id), fromRole: "rider" })
    .sort({ createdAt: -1 })
    .toArray();
  res.json(reviews);
}));

// Get all reviews a rider has received from drivers
app.get("/api/rider/:email/reviews", asyncRoute(async (req, res) => {
  const reviews = await reviewsCollection
    .find({ riderEmail: req.params.email.trim().toLowerCase(), fromRole: "driver" })
    .sort({ createdAt: -1 })
    .toArray();
  res.json(reviews);
}));

// Rider-facing: their own rating + account standing — what a Safety/Account
// screen shows ("your rating is 3.2 — your account is under review").
// Runs the lazy deactivation resolver first so this is always current.
app.get("/api/riders/:email/status", asyncRoute(async (req, res) => {
  const normalizedEmail = req.params.email.trim().toLowerCase();
  let user = await usersCollection.findOne({ email: normalizedEmail, role: "rider" });
  if (!user) return res.status(404).json({ error: "Rider not found" });
  user = await resolveRiderDeactivation(user);

  res.json({
    email: user.email,
    accountStatus: user.accountStatus || "active",
    rating: user.rating ?? null,
    ratingCount: user.ratingCount ?? 0,
    deactivationWarnedAt: user.deactivationWarnedAt || null,
    deactivationDeadline: user.deactivationDeadline || null,
    appealTicketId: user.appealTicketId || null,
  });
}));

// Rider files an appeal against a deactivation warning/decision. Reuses
// the support ticket system built for #5 as the audit trail and review
// channel — "high" priority (real, but not a safety emergency), tied back
// to the account via appealTicketId so the 7-day clock in
// resolveRiderDeactivation pauses while it's open.
app.post("/api/riders/:email/appeal", asyncRoute(async (req, res) => {
  const { message } = req.body;
  if (!message?.trim()) throw badRequest("message is required");

  const normalizedEmail = req.params.email.trim().toLowerCase();
  let user = await usersCollection.findOne({ email: normalizedEmail, role: "rider" });
  if (!user) return res.status(404).json({ error: "Rider not found" });
  user = await resolveRiderDeactivation(user);

  if (!["pending_deactivation", "deactivated"].includes(user.accountStatus)) {
    throw badRequest("There's no deactivation warning on this account to appeal");
  }
  if (user.appealTicketId) {
    const existingTicket = await supportTicketsCollection.findOne({ _id: user.appealTicketId });
    if (existingTicket && !["resolved", "closed"].includes(existingTicket.status)) {
      throw badRequest("You already have an appeal in review");
    }
  }

  const now = new Date();
  const priority = "high";
  const { firstResponseDueAt, resolutionDueAt } = slaDeadlines(priority, now);
  const ticket = {
    raisedByRole: "rider",
    raisedByEmail: normalizedEmail,
    raisedByName: user.name || null,
    rideId: null,
    category: "account_appeal",
    priority,
    subject: "Rider account deactivation appeal",
    description: message.trim().slice(0, 3000),
    status: "open",
    assignedTo: null,
    firstRespondedAt: null,
    resolvedAt: null,
    closedAt: null,
    firstResponseDueAt,
    resolutionDueAt,
    createdAt: now,
    accountStatusAtFiling: user.accountStatus,
    ratingAtFiling: user.rating ?? null,
  };
  const ticketResult = await supportTicketsCollection.insertOne(ticket);
  await supportTicketMessagesCollection.insertOne({
    ticketId: ticketResult.insertedId,
    senderRole: "rider",
    senderName: user.name || null,
    text: ticket.description,
    createdAt: now,
  });
  await usersCollection.updateOne(
    { email: normalizedEmail },
    { $set: { appealTicketId: ticketResult.insertedId, appealFiledAt: now } }
  );

  res.json({ message: "Appeal submitted — we'll review your account", ticketId: ticketResult.insertedId });
}));

// Admin: the binding decision on a rider's appeal. Reinstating clears the
// deactivation entirely; upholding finalizes it. Either way, the linked
// support ticket is closed out with the decision as the last message, so
// the whole review lives in one auditable thread.
app.post("/api/admin/riders/:email/appeal-decision", requireAdmin, asyncRoute(async (req, res) => {
  const { decision, note } = req.body; // "reinstate" | "uphold"
  if (!["reinstate", "uphold"].includes(decision)) {
    throw badRequest('decision must be "reinstate" or "uphold"');
  }

  const normalizedEmail = req.params.email.trim().toLowerCase();
  const user = await usersCollection.findOne({ email: normalizedEmail, role: "rider" });
  if (!user) return res.status(404).json({ error: "Rider not found" });

  const now = new Date();
  const update = decision === "reinstate"
    ? { accountStatus: "active", deactivationWarnedAt: null, deactivationDeadline: null, appealTicketId: null }
    : { accountStatus: "deactivated" };
  await usersCollection.updateOne({ email: normalizedEmail }, { $set: update });

  if (user.appealTicketId) {
    await supportTicketsCollection.updateOne(
      { _id: user.appealTicketId },
      { $set: { status: "resolved", resolvedAt: now } }
    );
    await supportTicketMessagesCollection.insertOne({
      ticketId: user.appealTicketId,
      senderRole: "agent",
      senderName: "Spring Support",
      text: note?.trim() || (decision === "reinstate" ? "Appeal approved — account reinstated." : "Appeal reviewed — deactivation upheld."),
      createdAt: now,
    });
  }

  res.json({ message: decision === "reinstate" ? "Appeal approved — account reinstated" : "Appeal denied — deactivation upheld" });
}));

// Driver-facing earnings dashboard. Everything here is computed from real
// ride records — nothing is a placeholder number. "Today" = since local
// midnight on the server; if your driver base spans multiple time zones,
// swap this for a per-driver timezone later.
app.get("/api/driver/:id/summary", asyncRoute(async (req, res) => {
  const driverId = toObjectId(req.params.id, "driver id");
  const driver = await driversCollection.findOne({ _id: driverId });
  if (!driver) return res.status(404).json({ error: "Driver not found" });

  const startOfToday = new Date();
  startOfToday.setHours(0, 0, 0, 0);

  const allRides = await ridesCollection.find({ driverId }).toArray();
  const completedToday = allRides.filter(
    (r) => r.status === "completed" && r.completedAt && new Date(r.completedAt) >= startOfToday
  );

  const grossFaresToday = completedToday.reduce((sum, r) => sum + (r.fare || 0), 0);
  const distanceTodayKm = completedToday.reduce((sum, r) => sum + (r.distanceKm || 0), 0);
  const fuelCostToday = Math.round(distanceTodayKm * FUEL_COST_PER_KM);
  const platformFeeToday = Math.round(grossFaresToday * PLATFORM_FEE_RATE);
  const netTakeHomeToday = Math.max(0, grossFaresToday - platformFeeToday - fuelCostToday);

  // Acceptance rate: of every ride ever routed to this driver, how many did
  // they accept (accepted/in_progress/completed) vs actively decline?
  // Requests still sitting as "requested" (not yet answered) don't count
  // either way.
  const answered = allRides.filter((r) => r.status !== "requested");
  const accepted = answered.filter((r) => r.status !== "declined");
  const acceptanceRate = answered.length ? Math.round((accepted.length / answered.length) * 100) : 100;

  // Online-time pay: guaranteed-minimum model. A driver's day is never
  // worth less than (online hours × rate) — trip earnings only get a
  // top-up when they fall short of that floor, never a flat add-on on top
  // of a day that already cleared it. onlineTimePayToday is kept as an
  // alias of the new onlineTimeTopUpToday field so any older client still
  // reading that name doesn't break.
  const onlineMinutesToday = await onlineMinutesSince(driverId, startOfToday);
  const onlineHoursToday = Math.round((onlineMinutesToday / 60) * 100) / 100;
  const guaranteedMinimumToday = Math.round((onlineMinutesToday / 60) * ONLINE_TIME_PAY_PER_HOUR_NAIRA);
  const onlineTimeTopUpToday = Math.max(0, guaranteedMinimumToday - netTakeHomeToday);
  const totalTakeHomeToday = netTakeHomeToday + onlineTimeTopUpToday; // == max(netTakeHomeToday, guaranteedMinimumToday)

  res.json({
    tripsToday: completedToday.length,
    grossFaresToday,
    platformFeeToday,
    fuelCostToday,
    netTakeHomeToday,
    onlineHoursToday,
    onlineTimePayRatePerHourNaira: ONLINE_TIME_PAY_PER_HOUR_NAIRA,
    guaranteedMinimumToday,
    onlineTimeTopUpToday,
    onlineTimePayToday: onlineTimeTopUpToday, // back-compat alias
    totalTakeHomeToday,
    acceptanceRate,
    rating: driver.rating ?? 5.0,
    totalTripsAllTime: allRides.filter((r) => r.status === "completed").length,
  });
}));

// ---------- SUPPORT SLA TRACKER ----------
// A rider or driver opens a ticket (optionally tied to a specific ride —
// e.g. disputing a cancellation fee), it gets a priority + two SLA
// deadlines at creation, and every read decorates it with live
// firstResponseBreached/resolutionBreached flags (see decorateTicketWithSla
// above) instead of relying on a background job to flip a stored flag.
// There's no auth/token layer anywhere else in this backend (login doesn't
// UPDATE: the admin routes below now require a valid admin JWT
// (requireAdmin, defined near the top of this file) — they used to trust
// the request body like everything else, but that's fixed now. The
// rider/driver-facing routes above and below still trust body.email;
// migrating those is the next hardening step, tracked separately.

// Rider or driver opens a new ticket.
app.post("/api/support/tickets", asyncRoute(async (req, res) => {
  const { raisedByRole, raisedByEmail, raisedByName, rideId, category, subject, description, priority } = req.body;
  if (!["rider", "driver"].includes(raisedByRole)) {
    throw badRequest('raisedByRole must be "rider" or "driver"');
  }
  if (!raisedByEmail?.trim()) throw badRequest("raisedByEmail is required");
  if (!VALID_TICKET_CATEGORIES.includes(category)) {
    throw badRequest(`category must be one of: ${VALID_TICKET_CATEGORIES.join(", ")}`);
  }
  if (!subject?.trim() || !description?.trim()) {
    throw badRequest("subject and description are required");
  }

  const linkedRideId = rideId ? toObjectId(rideId, "ride id") : null;
  const effectivePriority = derivePriority(category, priority);
  const now = new Date();
  const { firstResponseDueAt, resolutionDueAt } = slaDeadlines(effectivePriority, now);

  const ticket = {
    raisedByRole,
    raisedByEmail: raisedByEmail.trim().toLowerCase(),
    raisedByName: raisedByName?.trim() || null,
    rideId: linkedRideId,
    category,
    priority: effectivePriority,
    subject: subject.trim().slice(0, 200),
    description: description.trim().slice(0, 3000),
    status: "open",
    assignedTo: null,
    firstRespondedAt: null,
    resolvedAt: null,
    closedAt: null,
    firstResponseDueAt,
    resolutionDueAt,
    createdAt: now,
  };
  const result = await supportTicketsCollection.insertOne(ticket);

  // The opening description doubles as the thread's first message so the
  // ticket detail view reads as one continuous conversation.
  await supportTicketMessagesCollection.insertOne({
    ticketId: result.insertedId,
    senderRole: raisedByRole,
    senderName: ticket.raisedByName,
    text: ticket.description,
    createdAt: now,
  });

  res.json({
    message: "Support ticket created",
    id: result.insertedId,
    ticket: decorateTicketWithSla({ ...ticket, _id: result.insertedId }),
  });
}));

// Rider/driver: their own ticket list (e.g. a "My Support Tickets" screen).
app.get("/api/support/tickets/:role/:email", asyncRoute(async (req, res) => {
  const { role, email } = req.params;
  if (!["rider", "driver"].includes(role)) throw badRequest('role must be "rider" or "driver"');

  const tickets = await supportTicketsCollection
    .find({ raisedByRole: role, raisedByEmail: email.trim().toLowerCase() })
    .sort({ createdAt: -1 })
    .toArray();
  res.json(tickets.map(decorateTicketWithSla));
}));

// One ticket + its full message thread.
app.get("/api/support/tickets/:id", asyncRoute(async (req, res) => {
  const ticketId = toObjectId(req.params.id, "ticket id");
  const ticket = await supportTicketsCollection.findOne({ _id: ticketId });
  if (!ticket) return res.status(404).json({ error: "Ticket not found" });

  const messages = await supportTicketMessagesCollection.find({ ticketId }).sort({ createdAt: 1 }).toArray();
  res.json({ ticket: decorateTicketWithSla(ticket), messages });
}));

// Reply on a ticket thread — rider/driver (the reporter) or an agent.
// An agent's FIRST reply is what stops the first-response SLA clock and
// bumps a brand-new ticket into "in_progress". If the original reporter
// writes back on a ticket already marked "resolved", that's a signal it
// wasn't actually resolved, so it reopens automatically rather than
// stranding their message on a dead ticket.
app.post("/api/support/tickets/:id/messages", asyncRoute(async (req, res) => {
  const { senderRole, senderName, text } = req.body; // "rider" | "driver" | "agent"
  if (!["rider", "driver", "agent"].includes(senderRole)) {
    throw badRequest('senderRole must be "rider", "driver" or "agent"');
  }
  if (!text?.trim()) throw badRequest("text is required");

  const ticketId = toObjectId(req.params.id, "ticket id");
  const ticket = await supportTicketsCollection.findOne({ _id: ticketId });
  if (!ticket) return res.status(404).json({ error: "Ticket not found" });
  if (ticket.status === "closed") {
    throw badRequest("This ticket is closed — open a new one instead of replying here");
  }

  const now = new Date();
  const message = {
    ticketId,
    senderRole,
    senderName: senderName?.trim() || null,
    text: text.trim().slice(0, 3000),
    createdAt: now,
  };
  await supportTicketMessagesCollection.insertOne(message);

  const update = {};
  if (senderRole === "agent" && !ticket.firstRespondedAt) update.firstRespondedAt = now;
  if (senderRole === "agent" && ticket.status === "open") update.status = "in_progress";
  if (senderRole === ticket.raisedByRole && ticket.status === "resolved") {
    update.status = "in_progress";
    update.resolvedAt = null;
  }
  if (Object.keys(update).length) {
    await supportTicketsCollection.updateOne({ _id: ticketId }, { $set: update });
  }

  res.json({ message: "Reply sent", data: message });
}));

// Admin/agent: move a ticket through open -> in_progress -> resolved ->
// closed (or reopen it), and optionally assign it. Moving back to
// open/in_progress clears resolvedAt/closedAt so the resolution clock is
// accurately "still running" again rather than showing a stale timestamp.
app.post("/api/support/tickets/:id/status", asyncRoute(async (req, res) => {
  const { status, assignedTo } = req.body;
  if (!VALID_TICKET_STATUSES.includes(status)) {
    throw badRequest(`status must be one of: ${VALID_TICKET_STATUSES.join(", ")}`);
  }

  const ticketId = toObjectId(req.params.id, "ticket id");
  const ticket = await supportTicketsCollection.findOne({ _id: ticketId });
  if (!ticket) return res.status(404).json({ error: "Ticket not found" });

  const now = new Date();
  const update = { status };
  if (typeof assignedTo === "string") update.assignedTo = assignedTo.trim() || null;
  if (status === "resolved" && !ticket.resolvedAt) update.resolvedAt = now;
  if (status === "closed") {
    update.closedAt = now;
    if (!ticket.resolvedAt) update.resolvedAt = now;
  }
  if (["open", "in_progress"].includes(status)) {
    update.resolvedAt = null;
    update.closedAt = null;
  }

  await supportTicketsCollection.updateOne({ _id: ticketId }, { $set: update });
  const updated = await supportTicketsCollection.findOne({ _id: ticketId });
  res.json({ message: `Ticket marked as ${status}`, ticket: decorateTicketWithSla(updated) });
}));

// Admin: triage queue across every ticket, optionally filtered. Sorted
// breached-first, then by priority, then oldest-first — the order a real
// support queue should be worked in.
app.get("/api/admin/support/tickets", requireAdmin, asyncRoute(async (req, res) => {
  const { status, priority, category, breachedOnly } = req.query;
  const query = {};
  if (status) {
    if (!VALID_TICKET_STATUSES.includes(status)) throw badRequest("invalid status filter");
    query.status = status;
  }
  if (priority) {
    if (!VALID_PRIORITIES.includes(priority)) throw badRequest("invalid priority filter");
    query.priority = priority;
  }
  if (category) {
    if (!VALID_TICKET_CATEGORIES.includes(category)) throw badRequest("invalid category filter");
    query.category = category;
  }

  const tickets = await supportTicketsCollection.find(query).sort({ createdAt: -1 }).limit(200).toArray();
  let decorated = tickets.map(decorateTicketWithSla);
  if (breachedOnly === "true") {
    decorated = decorated.filter((t) => t.firstResponseBreached || t.resolutionBreached);
  }

  const priorityRank = { urgent: 0, high: 1, normal: 2 };
  decorated.sort((a, b) => {
    const aBreached = a.firstResponseBreached || a.resolutionBreached;
    const bBreached = b.firstResponseBreached || b.resolutionBreached;
    if (aBreached !== bBreached) return aBreached ? -1 : 1;
    if (priorityRank[a.priority] !== priorityRank[b.priority]) return priorityRank[a.priority] - priorityRank[b.priority];
    return new Date(a.createdAt) - new Date(b.createdAt);
  });

  res.json(decorated);
}));

// Admin: SLA compliance dashboard — current breach counts plus historical
// hit-rate and average-time stats, computed from real ticket records only.
app.get("/api/admin/support/summary", requireAdmin, asyncRoute(async (req, res) => {
  const tickets = (await supportTicketsCollection.find({}).toArray()).map(decorateTicketWithSla);

  const statusCounts = { open: 0, in_progress: 0, resolved: 0, closed: 0 };
  tickets.forEach((t) => { statusCounts[t.status] = (statusCounts[t.status] || 0) + 1; });

  const active = tickets.filter((t) => !["resolved", "closed"].includes(t.status));
  const resolvedOrClosed = tickets.filter((t) => t.resolvedAt);
  const everResponded = tickets.filter((t) => t.firstRespondedAt);

  const avgMinutesBetween = (list, endField) => {
    const durations = list
      .filter((t) => t[endField])
      .map((t) => (new Date(t[endField]) - new Date(t.createdAt)) / 60000);
    if (!durations.length) return null;
    return Math.round(durations.reduce((sum, d) => sum + d, 0) / durations.length);
  };

  res.json({
    statusCounts,
    breachedRightNow: {
      firstResponse: active.filter((t) => t.firstResponseBreached).length,
      resolution: active.filter((t) => t.resolutionBreached).length,
    },
    compliance: {
      firstResponseMetRate: everResponded.length
        ? Math.round((everResponded.filter((t) => t.firstResponseMet).length / everResponded.length) * 100)
        : null,
      resolutionMetRate: resolvedOrClosed.length
        ? Math.round((resolvedOrClosed.filter((t) => t.resolutionMet).length / resolvedOrClosed.length) * 100)
        : null,
    },
    avgFirstResponseMinutes: avgMinutesBetween(everResponded, "firstRespondedAt"),
    avgResolutionMinutes: avgMinutesBetween(resolvedOrClosed, "resolvedAt"),
    byPriority: VALID_PRIORITIES.map((p) => ({
      priority: p,
      total: tickets.filter((t) => t.priority === p).length,
      breachedRightNow: active.filter((t) => t.priority === p && (t.firstResponseBreached || t.resolutionBreached)).length,
    })),
  });
}));

// ---------- PLACES (server-side proxy for Google Places) ----------
// The mobile app used to call Google's Places Web Service directly with the
// same key given to the Android Maps SDK. That key is (correctly)
// restricted to the Android app's package name + SHA-1 fingerprint, which
// Google can verify for native SDK calls but NOT for a plain HTTPS request
// coming from JS — so those requests were silently failing with
// REQUEST_DENIED and the app just showed no results. Proxying through here
// lets us use a separate, server-side key instead.
//
// This uses Places API (NEW) — the legacy Places endpoints
// (maps/api/place/...) are unavailable on newly created Google Cloud
// projects, so New is the only reliable option going forward. Make sure
// "Places API (New)" (NOT "Places API") is enabled for GOOGLE_PLACES_API_KEY
// in Google Cloud Console → APIs & Services → Library.
const PLACES_KEY = process.env.GOOGLE_PLACES_API_KEY;
const PLACES_BIAS_LAT = 5.49; // South-East Nigeria, Spring's operating area
const PLACES_BIAS_LNG = 7.20;
const PLACES_BIAS_RADIUS = 50000.0; // meters — Google's max allowed for locationBias.circle

app.get("/api/places/autocomplete", asyncRoute(async (req, res) => {
  if (!PLACES_KEY) return res.status(500).json({ error: "GOOGLE_PLACES_API_KEY is not configured on the server" });
  const { query } = req.query;
  if (!query || query.trim().length < 2) return res.json({ predictions: [] });

  const googleRes = await fetch("https://places.googleapis.com/v1/places:autocomplete", {
    method: "POST",
    headers: { "Content-Type": "application/json", "X-Goog-Api-Key": PLACES_KEY },
    body: JSON.stringify({
      input: query,
      includedRegionCodes: ["ng"],
      locationBias: { circle: { center: { latitude: PLACES_BIAS_LAT, longitude: PLACES_BIAS_LNG }, radius: PLACES_BIAS_RADIUS } },
    }),
  });
  const data = await googleRes.json();
  if (!googleRes.ok) {
    console.error("Places autocomplete error:", data.error?.message || data);
    return res.status(502).json({ error: data.error?.message || "Places autocomplete failed" });
  }

  const predictions = (data.suggestions || [])
    .filter((s) => s.placePrediction)
    .map((s) => {
      const p = s.placePrediction;
      return {
        placeId: p.placeId,
        mainText: p.structuredFormat?.mainText?.text || p.text?.text,
        secondaryText: p.structuredFormat?.secondaryText?.text || "",
        description: p.text?.text,
      };
    });
  res.json({ predictions });
}));

app.get("/api/places/details", asyncRoute(async (req, res) => {
  if (!PLACES_KEY) return res.status(500).json({ error: "GOOGLE_PLACES_API_KEY is not configured on the server" });
  const { placeId } = req.query;
  if (!placeId) throw badRequest("placeId is required");

  const googleRes = await fetch(`https://places.googleapis.com/v1/places/${encodeURIComponent(placeId)}`, {
    headers: { "X-Goog-Api-Key": PLACES_KEY, "X-Goog-FieldMask": "displayName,formattedAddress,location" },
  });
  const data = await googleRes.json();
  if (!googleRes.ok) {
    console.error("Places details error:", data.error?.message || data);
    return res.status(502).json({ error: data.error?.message || "Places details failed" });
  }
  res.json({ name: data.displayName?.text, address: data.formattedAddress, lat: data.location.latitude, lng: data.location.longitude });
}));

app.get("/api/places/nearby", asyncRoute(async (req, res) => {
  if (!PLACES_KEY) return res.status(500).json({ error: "GOOGLE_PLACES_API_KEY is not configured on the server" });
  const { lat, lng, radius } = req.query;
  if (!lat || !lng) throw badRequest("lat and lng are required");

  const googleRes = await fetch("https://places.googleapis.com/v1/places:searchNearby", {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      "X-Goog-Api-Key": PLACES_KEY,
      "X-Goog-FieldMask": "places.id,places.displayName,places.location,places.rating",
    },
    body: JSON.stringify({
      locationRestriction: { circle: { center: { latitude: parseFloat(lat), longitude: parseFloat(lng) }, radius: parseFloat(radius) || 4000.0 } },
      rankPreference: "POPULARITY",
      maxResultCount: 10,
    }),
  });
  const data = await googleRes.json();
  if (!googleRes.ok) {
    console.error("Places nearby error:", data.error?.message || data);
    return res.status(502).json({ error: data.error?.message || "Places nearby failed" });
  }

  res.json({
    results: (data.places || []).map((p) => ({
      placeId: p.id,
      name: p.displayName?.text,
      lat: p.location?.latitude,
      lng: p.location?.longitude,
      rating: p.rating,
    })),
  });
}));

// ---------- SPRING WALLET ----------
// A simple in-house balance + ledger. There's no real payment processor
// wired in yet, so "Top up" here is a manual/simulated credit (clearly
// labeled as such to the rider) rather than a real card charge — swap the
// topup handler for a real payment gateway webhook when Spring adds one.

app.get("/api/wallet/:email", asyncRoute(async (req, res) => {
  const normalizedEmail = req.params.email.trim().toLowerCase();
  const wallet = await walletsCollection.findOneAndUpdate(
    { email: normalizedEmail },
    { $setOnInsert: { email: normalizedEmail, balance: 0, createdAt: new Date() } },
    { upsert: true, returnDocument: "after" }
  );
  const transactions = await walletTransactionsCollection
    .find({ email: normalizedEmail })
    .sort({ createdAt: -1 })
    .limit(50)
    .toArray();
  res.json({ balance: wallet.balance, transactions });
}));

app.post("/api/wallet/:email/topup", asyncRoute(async (req, res) => {
  const normalizedEmail = req.params.email.trim().toLowerCase();
  const { amount } = req.body;
  if (typeof amount !== "number" || amount <= 0) throw badRequest("amount must be a positive number");

  await walletsCollection.updateOne(
    { email: normalizedEmail },
    { $setOnInsert: { email: normalizedEmail, createdAt: new Date() }, $inc: { balance: Math.round(amount) } },
    { upsert: true }
  );
  const tx = {
    email: normalizedEmail,
    type: "topup",
    amount: Math.round(amount),
    note: "Wallet top-up (simulated — no real payment gateway connected yet)",
    createdAt: new Date(),
  };
  await walletTransactionsCollection.insertOne(tx);
  const wallet = await walletsCollection.findOne({ email: normalizedEmail });
  res.json({ message: "Wallet topped up", balance: wallet.balance, transaction: tx });
}));

// ---------- SPRING SEND (package / waybill delivery) ----------
// Reuses the ridesCollection so the whole accept/decline/status/chat
// pipeline built for rides works unchanged for packages — a package is
// just a ride with type: "package" plus a few package-only fields.

app.post("/api/packages/request", asyncRoute(async (req, res) => {
  const { riderEmail, riderName, driverId, pickup, destination, pickupLocation, destinationLocation, size, price, recipientName, recipientPhone, note } = req.body;
  if (!riderEmail || !driverId || !pickup?.trim() || !destination?.trim() || !size) {
    throw badRequest("riderEmail, driverId, pickup, destination and size are required");
  }
  if (!["small", "medium", "large"].includes(size)) {
    throw badRequest('size must be "small", "medium" or "large"');
  }
  await assertRiderNotDeactivated(riderEmail.trim().toLowerCase());

  const driver = await driversCollection.findOne({ _id: toObjectId(driverId, "driver id") });
  if (!driver || !driver.online) {
    throw badRequest("That driver is no longer available");
  }

  const newPackage = {
    type: "package",
    riderEmail: riderEmail.trim().toLowerCase(),
    riderName,
    driverId: driver._id,
    driverName: driver.name,
    pickup: pickup.trim(),
    destination: destination.trim(),
    pickupLocation: pickupLocation && typeof pickupLocation.lat === "number" ? pickupLocation : null,
    destinationLocation: destinationLocation && typeof destinationLocation.lat === "number" ? destinationLocation : null,
    packageSize: size,
    recipientName: recipientName?.trim() || null,
    recipientPhone: recipientPhone?.trim() || null,
    note: note?.trim().slice(0, 500) || null,
    estimatedFare: typeof price === "number" ? Math.round(price) : null,
    status: "requested",
    distanceKm: null,
    fare: null,
    createdAt: new Date(),
  };
  const result = await ridesCollection.insertOne(newPackage);
  res.json({ message: "Package requested!", id: result.insertedId, ride: { ...newPackage, _id: result.insertedId } });
}));

app.get("/api/packages/rider/:riderEmail", asyncRoute(async (req, res) => {
  const packages = await ridesCollection
    .find({ riderEmail: req.params.riderEmail.trim().toLowerCase(), type: "package" })
    .sort({ createdAt: -1 })
    .toArray();
  res.json(packages);
}));

app.use((req, res) => {
  res.status(404).json({ error: "Not found" });
});

// Centralized error handler — every asyncRoute()-wrapped handler above ends
// up here on failure, so callers always get clean JSON instead of a raw
// stack trace or a hung connection.
app.use((err, req, res, next) => {
  if (err.code === 11000) {
    return res.status(400).json({ error: "That email is already registered" });
  }
  const status = err.status || 500;
  if (status === 500) console.error(err);
  res.status(status).json({ error: status === 500 ? "Something went wrong" : err.message });
});

app.listen(PORT, () => {
  console.log(`Server is running on http://localhost:${PORT}`);
});
