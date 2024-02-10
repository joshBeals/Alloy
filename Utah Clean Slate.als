
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
abstract sig ClassAMisdemeanor extends Conviction { }
abstract sig ClassBMisdemeanor extends Conviction { }
abstract sig ClassCMisdemeanor extends Conviction { }
abstract sig Infraction extends Conviction { }
abstract sig DrugPossessionOffense extends Conviction {}

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
	withinFive: set Date,		-- the events occurring within 5 years of this date
	withinSix: set Date,		-- the events occurring within 6 years of this date
	withinSeven: set Date		-- the events occurring within 7 years of this date
}
-- Pairs of dates that are not within 6
fun beyondSix: Date->Date {
	(^(ordering/next) & Date->Date) - withinSix
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
	irreflexive[withinFive + withinSix + withinSeven]
	-- every date within 5 years is also within 6 years
	withinFive in withinSix
	-- the within-5 relation is compatible with the ordering on Dates
	withinFive.compatibleWithOrdering
	-- every date within 6 years is also within 7 years
	withinSix in withinSeven
	-- the within-6 relation is compatible with the ordering on Dates
	withinSix.compatibleWithOrdering
	-- the within-7 relation is compatible with the ordering on Dates
	withinSeven.compatibleWithOrdering
	-- some arithmetic for ordered dates A-B-C:
	-- if A-B and B-C are both beyond 5, A-C is not within 6
	no withinSix & beyondFive.beyondFive
	-- if A-B is beyond 5 and B-C is beyond 6, A-C is not within 7
	no withinSeven & (beyondFive.beyondSix + beyondSix.beyondFive)
	-- if A-B and B-C are both within 3, A-C is within 7
	--withinThree.withinThree in withinSeven
	-- every date is associated with at least one event
	Date in Event.date
	--lone (Date - Event.date) -- *** This is a hack ***
	-- All events happening now have the same date
	always (some now implies one now.date)
	-- Date ordering is consistent with event ordering
	all e1, e2: Event | hb[e1, e2] implies e1.date.lt[e2.date]
}


pred expungedWithinFive[c: Conviction] {
	((c in ClassCMisdemeanor) or (c in Infraction)) and  c.expunged and c.exp.date in c.date.withinFive
}
pred expungedWithinSix[c: ClassBMisdemeanor] {
	c.expunged and c.exp.date in c.date.withinSix
}
pred expungedWithinSeven[c: Conviction] {
	((c in ClassAMisdemeanor) or (c in Felony)) c.expunged and c.exp.date in c.date.withinSeven
}

-- Expungemnt Limit Cases

--Case 1: Two or more felony (except drug possesion offenses).
pred case1[c: Conviction] {
	some f1, f2: Felony |
		#(f1 + f2) = 2 and hb[f1, c] and hb[f2, c]
}
--Case 2: Any combination of three or more convictions (except drug possesion offenses) that includes two class A misdemeanors.
pred case2[c:Conviction]{
	some disj c1, c2, c3: Conviction |
		hb[c1, c2] and hb[c2, c3] and hb[c3, c] and
		(#(DrugPossessionOffense & (c1 + c2 + c3)) = 0) and (#(ClassAMisdemeanor & (c1 + c2 + c3)) = 2)
}
--Case 3: Any combination of four or more convictions (except drug possesion offenses) that includes three class B misdemeanors.
pred case3[c:Conviction]{
	some disj c1, c2, c3, c4: Conviction |
		hb[c1, c2] and hb[c2, c3] and hb[c3, c4] and hb[c4, c] and
		(#(DrugPossessionOffense & (c1 + c2 + c3 + c4)) = 0) and (#(ClassBMisdemeanor & (c1 + c2 + c3 + c4)) = 3)
}
--Case 4: Five or more convictions (except drug possesion offenses). Could be mix of misdemeanors and felony.
pred case4[c:Conviction]{
	some disj c1, c2, c3, c4: Conviction |
		hb[c1, c2] and hb[c2, c3] and hb[c3, c4] and hb[c4, c] and
		(#(DrugPossessionOffense & (c1 + c2 + c3 + c4)) = 0) and (#(ClassBMisdemeanor & (c1 + c2 + c3 + c4)) = 3)
}

fact {
	no f: Felony | expungedWithinSeven[f]
	no c: ClassAMisdemeanor | expungedWithinSeven[c]
	no c: ClassBMisdemeanor | expungedWithinSix[c]
	no c: ClassCMisdemeanor | expungedWithinFive[c]
	no i: Infraction | expungedWithinFive[i]
	
	no c: Conviction | case1[c] and expunged[c]
	no c: Conviction | case2[c] and expunged[c]
	no c: Conviction | case3[c] and expunged[c]
	no c: Conviction | case4[c] and expunged[c]
}

--Case 5: Three or more felony convictions for drug possession offenses.
--Case 6: Any combination of five or more convictions for drug possession offenses.

pred show{
	eventually some c: Conviction | c.expunged
}

run case3 for 5




