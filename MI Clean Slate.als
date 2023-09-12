module expunge

open util/relation
open util/ordering[Date]	-- Dates are linearly ordered

-- An event is a conviction or an expungement
abstract sig Event { 
	date: one Date -- each event has an associated date
}

-- now indicates the current event
var sig now in Event { } 

-- The strict happens-before relation for events (no reflexive pairs)
pred hb[e1, e2: Event] {
	eventually (e1 in now and after eventually e2 in now)
}

-- Well-behaved events
fact {
	-- Once events stop, they stop forever
	always (no now implies always no now)
	-- Every event occurs exactly once
	all e: Event | eventually (e in now and after always e not in now)
}

-- A conviction is a felony or a misdemeanor
abstract sig Conviction extends Event { }

abstract sig Felony extends Conviction { }
-- Special types of felony: assaultive, ten-year
sig AssaultiveFelony in Felony { }
sig TenYearFelony in Felony { }

abstract sig Misdemeanor extends Conviction { }
-- Special type of misdemeanor: OWI (Operating While Intoxicated)
sig OWI in Misdemeanor { }

sig Expungement extends Event {
	con: some Conviction -- the convictions that are being expunged
	-- note: multiple convictions may be expunged in a single event
}

-- Is the conviction c (eventually) expunged?
pred expunged[c: Conviction] {
	some con.c
}
fun exp: Conviction->Expungement {
	~con
}

-- Well-behaved convictions and expungements
fact {
	-- Convictions and expungements do not happen simultaneously
	always (now in Conviction or now in Expungement or no now)
	-- Every expungement is expunging a preceding conviction
	all x: Expungement | hb[x.con, x]
	-- Every conviction is expunged at most once
	all c: Conviction | lone c.exp
}

sig Date {
	withinThree: set Date,	-- the events occurring within 3 years of this date
	withinFive: set Date,		-- the events occurring within 5 years of this date
	withinSeven: set Date		-- the events occurring within 7 years of this date
}
-- Pairs of dates that are not within 3
fun beyondThree: Date->Date {
	(^(ordering/next) & Date->Date) - withinThree
}
-- Pairs of dates that are not within 5
fun beyondFive: Date->Date {
	(^(ordering/next) & Date->Date) - withinFive
}
fun nextDate: Date->Date {
	ordering/next & Date->Date 
}
pred compatibleWithOrdering[r: Date->Date] {
	-- r is a subset of the ordering relation on Dates  
	r in ^(ordering/next)
	-- for any ordered dates d1-d2-d3, if d1-d3 is in r, then d1-d2 and d2-d3 are as well
	all d1: Date | all d2: d1.^ordering/next | all d3: d2.^ordering/next |
		d3 in d1.r implies d2 in d1.r and d3 in d2.r
}
-- Well-behaved dates
fact {
	-- the within relations are all strict; no reflexive pairs
	irreflexive[withinThree + withinFive + withinSeven]
	-- every date within 3 years is also within 5 years
	withinThree in withinFive
	-- the within-3 relation is compatible with the ordering on Dates
	withinThree.compatibleWithOrdering
	-- every date within 5 years is also within 7 years
	withinFive in withinSeven
	-- the within-5 relation is compatible with the ordering on Dates
	withinFive.compatibleWithOrdering
	-- the within-7 relation is compatible with the ordering on Dates
	withinSeven.compatibleWithOrdering
	-- some arithmetic for ordered dates A-B-C:
	-- if A-B and B-C are both beyond 3, A-C is not within 5
	no withinFive & beyondThree.beyondThree
	-- if A-B is beyond 3 and B-C is beyond 5, A-C is not within 7
	no withinSeven & (beyondThree.beyondFive + beyondFive.beyondThree)
	-- if A-B and B-C are both within 3, A-C is within 7
	withinThree.withinThree in withinSeven
	-- every date is associated with at least one event
	Date in Event.date
	--lone (Date - Event.date) -- *** This is a hack ***
	-- All events happening now have the same date
	always (some now implies one now.date)
	-- Date ordering is consistent with event ordering
	all e1, e2: Event | hb[e1, e2] implies e1.date.lt[e2.date]
}


pred afterNEvents[E: Event, e: Event, n: Int] {
   	n = 1 implies afterFirstEvent[E, e]
   	n = 2 implies afterSecondEvent[E, e]
   	n = 3 implies afterThirdEvent[E, e]
   	n = 4 implies afterFourthEvent[E, e]
   	n = 5 implies afterFifthEvent[E, e]
   	n = 6 implies afterSixthEvent[E, e]
   	n = 7 implies afterSeventhEvent[E, e]
   	n > 7 implies afterEightEvent[E, e]
}

-- Does the Event e occur after 1 preceding events E?
pred afterFirstEvent[E: Event, e: Event] {
  some e1: E |
    hb[e1, e]
}

-- Does the Event e occur after 2 preceding events E?
pred afterSecondEvent[E: Event, e: Event] {
  some e1: E |
    afterFirstEvent[E, e] and hb[e1, e] and no e2: E |
      afterFirstEvent[E, e] and hb[e2, e] and e1 != e2
}

-- Does the Event e occur after 3 preceding events E?
pred afterThirdEvent[E: Event, e: Event] {
  some e1: E |
    afterSecondEvent[E, e] and hb[e1, e] and no e2: E |
      afterSecondEvent[E, e] and hb[e2, e] and e1 != e2
}

-- Does the Event e occur after 4 preceding events E?
pred afterFourthEvent[E: Event, e: Event] {
  some e1: E |
    afterThirdEvent[E, e] and hb[e1, e] and no e2: E |
      afterThirdEvent[E, e] and hb[e2, e] and e1 != e2
}

-- Does the Event e occur after 5 preceding events E?
pred afterFifthEvent[E: Event, e: Event] {
  some e1: E |
    afterFourthEvent[E, e] and hb[e1, e] and no e2: E |
      afterFourthEvent[E, e] and hb[e2, e] and e1 != e2
}

-- Does the Event e occur after 6 preceding events E?
pred afterSixthEvent[E: Event, e: Event] {
  some e1: E |
    afterFifthEvent[E, e] and hb[e1, e] and no e2: E |
      afterFifthEvent[E, e] and hb[e2, e] and e1 != e2
}

-- Does the Event e occur after 7 preceding events E?
pred afterSeventhEvent[E: Event, e: Event] {
  some e1: E |
    afterSixthEvent[E, e] and hb[e1, e] and no e2: E |
      afterSixthEvent[E, e] and hb[e2, e] and e1 != e2
}

-- Does the Event e occur after 8 preceding events E?
pred afterEightEvent[E: Event, e: Event] {
  some e1: E |
    afterSeventhEvent[E, e] and hb[e1, e] and no e2: E |
      afterSeventhEvent[E, e] and hb[e2, e] and e1 != e2
}

-- Does the conviction c occur after three preceding felonies?
--pred afterThirdFelony[c: Conviction] {
--	some f1, f2, f3: Felony |
		--#(f1 + f2 + f3) = 3 and hb[f1, c] and hb[f2, c] and hb[f3, c]
--}

pred noExpungedAfterNEvents[E: Event, E1: Event, N: Int] {
    no e: E | afterNEvents[E, E1, N] and expunged[e]
}

--No conviction may be expunged after three or more felonies (Sec. 1, 1a).
--pred sec1_1a {	
--	no c: Conviction | afterThirdFelony[c] and expunged[c]
--}

pred sec1_1a {
   noExpungedAfterNEvents[Felony, Conviction, 5]
}

-- Does the assaultive felony af occur after two preceding assaultive felonies?
--pred afterSecondAssault[af: AssaultiveFelony] {
	--some af1, af2: AssaultiveFelony |
		--af1 != af2 and hb[af1, af] and hb[af2, af]

   -- some af1, af2: AssaultiveFelony |
       -- af1 != af2 and afterNEvents[AssaultiveFelony, af1 + af2, 2]
--}
-- No more than two assaultive felonies may be expunged (Sec. 1, 1b).
--pred sec1_1b {
	--no af: AssaultiveFelony | afterSecondAssault[af] and expunged[af]
--}
pred sec1_1b {
    noExpungedAfterNEvents[AssaultiveFelony, AssaultiveFelony, 2]
}

-- Does the ten-year felony ty occur after a preceding ten-year felony?
pred afterFirstTenner[ty: TenYearFelony] {
	some ty1: TenYearFelony - ty | hb[ty1, ty]
}
-- Only one ten year felony may be expunged (Sec. 1, 1c).
pred sec1_1c {
	no ty: TenYearFelony | afterFirstTenner[ty] and expunged[ty]
}

-- Does the OWI occur after a preceding OWI?
pred afterFirstOWI[owi: OWI] {
	some owi1: OWI | hb[owi1, owi]
}
-- Only one OWI may be expunged (Sec. 1d, 2abcd).
pred sec1d_2 {
	no owi: OWI | afterFirstOWI[owi] and expunged[owi]
}

-- Is the misdemeanor m expunged within three years?
pred expungedWithinThree[m: Misdemeanor] {
	m.expunged and m.exp.date in m.date.withinThree
}
-- Is the felony f expunged within five years?
pred expungedWithinFive[f: Felony] {
	f.expunged and f.exp.date in f.date.withinFive
}
-- Is the felony f expunged within seven years?
pred expungedWithinSeven[f: Felony] {
	f.expunged and f.exp.date in f.date.withinSeven
}
-- Is there an additional, intervening felony between felony f and event e?
pred interveningFelony[f: Felony, e: Event] {
	some f1: Felony | hb[f, f1] and hb[f1, e]
}
pred sec1d_timing {
	no m: Misdemeanor | expungedWithinThree[m]
	no f: Felony | expungedWithinFive[f]
	no f: Felony | interveningFelony[f, f.exp] and expungedWithinSeven[f]
}

pred backwardWaiting {
	no x: Expungement |
		(some m: Misdemeanor | x.date in m.date.withinThree)
		or (some f: Felony | x.date in f.date.withinFive)
		or (some f: Felony | interveningFelony[f, x] and x.date in f.date.withinSeven)
}

pred forwardWaiting {
	all m: Misdemeanor | m.expunged implies no c: Conviction | c.date in m.date.withinThree
	all f: Felony | f.expunged implies no c: Conviction | c.date in f.date.withinFive
	all f1: Felony | f1.expunged implies no f2: Felony | f2.date in f1.date.withinSeven
}

-- The constraints of MCL 780.621 hold in the model.
fact {
	sec1_1a
	sec1_1b 
	sec1_1c 
	sec1d_2
	sec1d_timing
}

pred show {
	--backwardWaiting
	--not forwardWaiting

	-- test whether now can have multiple events
	--eventually not lone now

	-- Q: is it possible to have 4 felonies expunged?
	-- A: Yes! because of the one-bad-night rule
	some f1, f2, f3, f4: Felony |
		#(f1+f2+f3+f4) = 4
		and (eventually f1 in now) and f1.expunged
		and (eventually f2 in now) and f2.expunged
		and (eventually f3 in now) and f3.expunged
		and (eventually f4 in now) and f4.expunged
	
	--some c: AssaultiveFelony, e: AssaultiveFelony | afterSecondEvent[e, c] and expunged[c]
}
--run afterThirdEvent for 3 Conviction, 3 Felony, 3 Event, 3 Date
run show for 5 Event, 3 Date
