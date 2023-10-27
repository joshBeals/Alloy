module rulesEngine

open util/relation
open util/ordering[Conviction]


// Define a signature for convictions
abstract sig Conviction{
	-- the events occurring within 7 years of this date
	withinSeven: set Conviction,
	-- the events occurring within 10 years of this date	
	withinTen: set Conviction,
	
}

// Define types of convictions
sig Misdemeanor extends Conviction{}
sig Felony extends Conviction{}
sig Invalid extends Conviction{}

// Convictions that are set aside or not
var sig setAside in Conviction { }
var sig unexpungable in Conviction { }	
lone var sig curr in Conviction { }	

-- Pairs of dates that are not within 7
fun beyondSeven: Conviction->Conviction {
	(^(ordering/next) & Conviction->Conviction) - withinSeven
}

-- Pairs of dates that are not within 10
fun beyondTen: Conviction->Conviction {
	(^(ordering/next) & Conviction->Conviction) - withinTen
}

fun nextConviction: Conviction->Conviction {
	ordering/next & Conviction->Conviction 
}

pred compatibleWithOrdering[r: Conviction->Conviction] {
	-- r is a subset of the ordering relation on Dates  
	r in ^(ordering/next)
	-- for any ordered dates d1-d2-d3, if d1-d3 is in r, then d1-d2 and d2-d3 are as well
	all d1: Conviction | all d2: d1.^ordering/next | all d3: d2.^ordering/next |
		d3 in d1.r implies d2 in d1.r and d3 in d2.r
}

fact {
	-- the within relations are all strict; no reflexive pairs
	irreflexive[withinSeven + withinTen]
	-- every date within 7 years is also within 10 years
	withinSeven in withinTen
	-- the within-7 relation is compatible with the ordering on Dates
	withinSeven.compatibleWithOrdering
	-- the within-10 relation is compatible with the ordering on Dates
	withinTen.compatibleWithOrdering
	-- some arithmetic for ordered dates A-B-C:
	-- if A-B and B-C are both beyond 7, A-C is not within 10
	no withinTen & beyondSeven.beyondSeven
}

fact {
	-- Initialize setAside to be empty
	no setAside
	-- Curr should reference the first Conviction at the begining
	curr = ordering/first
}

pred blocked[c: Conviction] {
	(c in Misdemeanor and (some cn: nextConviction[c] | cn in c.withinSeven and not cn in setAside)
		or convictionLimit[curr])
	or
	(c in Felony and (some cn: nextConviction[c] | cn in c.withinTen and not cn in setAside)
		or convictionLimit[curr])
	or
	(c in Invalid)
}

pred firstUnexpunged[c1, c2: Conviction] {
	ordering/lte[c1, c2]
	not c2 in setAside
	no c3: Conviction | ordering/lte[c1, c3] and ordering/lt[c3, c2] and not c3 in setAside
}

pred convictionLimit[c: Conviction]{
	(c in Misdemeanor and (some m1, m2, m3, m4: Misdemeanor | #(m1 + m2 + m3 + m4) = 4 
		and	(m1 in setAside and m2 in setAside and m3 in setAside and m4 in setAside)))
	or
	(c in Felony and (some f1, f2: Felony | #(f1 + f2) = 2 and (f1 in setAside and f2 in setAside)))
}

fact {
	always ((some c: Conviction | firstUnexpunged[ordering/next[curr], c]) implies
		firstUnexpunged[ordering/next[curr], curr'])
	always ((no c: Conviction | firstUnexpunged[ordering/next[curr], c]) and (some c: Conviction | firstUnexpunged[ordering/first, c]) implies
		firstUnexpunged[ordering/first, curr'])
	always ((no c: Conviction | firstUnexpunged[ordering/first, c]) implies no curr')

	always (blocked[curr] implies setAside' = setAside)
	always (not blocked[curr] implies setAside' = setAside + curr)

	always (convictionLimit[curr] implies not curr in setAside)
	always (convictionLimit[curr] implies unexpungable' = unexpungable + curr)
	
	always (all c: Conviction | c in unexpungable' implies always c in unexpungable')
	all i: Invalid | always i in unexpungable'
}

pred expungedWithinSeven[m: Misdemeanor] {
	m in setAside' and nextConviction[m] in m.withinSeven
}

pred expungedWithinTen[f: Felony] {
	f in setAside' and nextConviction[f] in f.withinTen
}

fact {
	no m: Misdemeanor | expungedWithinSeven[m]
	no f: Felony | expungedWithinTen[f]
}

pred show {
	eventually some setAside
	--always some Conviction - setAside
}

run show for 3 Felony, 3 Misdemeanor, 1 Invalid

// Check expungement for the initialized convictions
--run show for 5 Conviction
