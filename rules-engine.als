module rulesEngine

open util/relation
open util/ordering[Conviction]

// Define a signature for convictions
abstract sig Conviction{
	-- the events occurring within 7 years of this date
	withinSeven: set Conviction,
	-- the events occurring within 10 years of this date	
	withinTen: set Conviction		
}

// Define types of convictions
sig Misdemeanor extends Conviction{}
sig Felony extends Conviction{}

// Convictions that are set aside or not
var sig setAside in Conviction { }	
var sig curr in Conviction { }	

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
	-- Curr should reference the first Conviction at the begining
	curr = ordering/first
	-- Each state should show a new curr Conviction
	all c: Conviction | eventually (curr = c and no other: Conviction - c | curr = other)
}

fact {
	-- Initialize setAside to be empty
	no setAside

	all c: Conviction | eventually (setAside' in c iff curr in c and 
		((c in Misdemeanor and c not in setAside and
			no cn: nextConviction[c] | cn in c.withinSeven)
			or
		(c in Felony and c not in setAside and
			no cn: nextConviction[c] | cn in c.withinTen)))

	--setAside' in curr iff 
		--(curr in Misdemeanor and curr not in setAside and
		--	no c: ordering/next[curr] | c in curr.withinSeven)
	--	or
		--(curr in Felony and curr not in setAside and
		--	no c: ordering/next[curr] | c in curr.withinTen)
}

pred show {

}

run show for 5 Conviction
