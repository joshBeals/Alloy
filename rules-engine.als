module rulesEngine

open util/boolean
open util/integer

sig Date {}

// Define a signature for conviction types
sig ConvictionType {}

// Define a signature for convictions
abstract sig Conviction{
    	date: Int,
    	type: one ConvictionType,
}

// Define types of convictions
sig Misdemeanor extends ConvictionType{}
sig Felony extends ConvictionType{}

// Convictions that are set aside or not
var sig setAside in Conviction { }		

// Define temporal logic for time intervals (e.g., 7 years)
pred withinSevenYears[c1, c2: Conviction] {
    c2.date - c1.date >= 0 and c2.date - c1.date < 7
}

pred withinTenYears[c1, c2: Conviction] {
    c2.date - c1.date >= 0 and c2.date - c1.date < 10
}

// Define temporal logic for time intervals (e.g., 7 years)
pred sevenYearsAgo[c: Conviction] {
    2023 - c.date <= 7
}

pred tenYearsAgo[c: Conviction] {
    2023 - c.date <= 10
}

// Expunge a conviction
pred expunge[c: Conviction] {
	-- Is Conviction c expunged?
	c not in setAside
	setAside' = setAside + c
}

// Define constraints for eligibility
pred isEligible(convictions: set Conviction) {
  // Check eligibility for each conviction in the set.
  all c1, c2: convictions |
    (c1.type = Misdemeanor and not sevenYearsAgo[c1] 
	and not withinSevenYears[c1, c2] implies expunge[c1]) or
    (c1.type = Felony and not tenYearsAgo[c1] 
	and not withinTenYears[c1, c2] implies expunge[c1])
}

// Define the order of convictions
fact OrderOfConvictions {
    all c1, c2: Conviction |
       c1 != c2 and c1.date <= c2.date
}

// Define the intervention of offenses


// Define the main predicate to check expungement
pred CheckExpungement[convictions: set Conviction] {
    all c: convictions |
        isEligible[c]
}

// Initialize convictions
pred show {
    some c1: Conviction | {
        c1.date = 2000 and c1.type = Misdemeanor
        some c2: Conviction | {
            c2.date = 2009 and c2.type = Misdemeanor
            some c3: Conviction | {
                c3.date = 2010 and c3.type = Felony
                some c4: Conviction | {
                    c4.date = 2010 and c4.type = Misdemeanor
                    some c5: Conviction | {
                        c5.date = 2011 and c5.type = Misdemeanor
                        some c6: Conviction | {
                            c6.date = 2012 and c6.type = Misdemeanor
                            some c7: Conviction | {
                                c7.date = 2012 and c7.type = Felony
                            }
                        }
                    }
                }
            }
        }
    }
}

// Check expungement for the initialized convictions
run show for 2 Conviction, 2 Date, 2 ConvictionType
