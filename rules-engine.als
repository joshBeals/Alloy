module engine

open util/boolean

// Define a signature for conviction types
sig ConvictionType {}

// Define a signature for convictions
abstract sig Conviction{
    date: Int,
    type: ConvictionType,
    setAside: Bool // Indicates whether the conviction has been set aside
}

// Define types of convictions
one sig Misdemeanor, Felony extends Conviction{}

// Define temporal logic for time intervals (e.g., 7 years)
pred SevenYearsAgo[c1, c2: Conviction] {
    c2.date - c1.date >= 0 and c2.date - c1.date < 7
}

// Define constraints for eligibility
pred EligibleForExpungement[c: Conviction] {
     // Rule: A maximum of four 93-day or more misdemeanors within 7 years
    Misdemeanor in c.type => {
        let sevenYearsAgo = c.date - 7 |
           #(c.date & Misdemeanor.date - sevenYearsAgo) <= 4
    }
    
    // Rule: A maximum of two felony convictions within 10 years
    Felony in c.type => {
        let tenYearsAgo = c.date - 10 |
            #(c.date & Felony.date - tenYearsAgo) <= 2
    }
}

// Define the order of convictions
fact OrderOfConvictions {
    all c1, c2: Conviction |
        c1.date <= c2.date
}

// Define the intervention of offenses
fact InterveningOffenses {
    all c1, c2: Conviction |
        c1.date <= c2.date and c1 != c2 =>
        not EligibleForExpungement[c2] => 
        no c3: Conviction |
            c1.date <= c3.date and c3.date <= c2.date
}

// Define the main predicate to check expungement
pred CheckExpungement[convictions: set Conviction] {
    all c1, c2: convictions |
        c1 != c2 implies not OrderOfExpungement[c1, c2]
        EligibleForExpungement[c1]
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
run show for 7 Conviction
