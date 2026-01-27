% Loan Eligibility Decision
% Determines if an applicant is eligible for a loan based on credit score and income

% Rule 1: High credit score, sufficient income
eligible_for_loan(Applicant, Amount, Result) :-
    Credit >= 700,
    Income >= Amount * 3,
    Result = approved.

% Rule 2: Good credit score, higher income requirement
eligible_for_loan(Applicant, Amount, Result) :-
    Credit >= 650,
    Credit < 700,
    Income >= Amount * 4,
    Result = approved.

% Rule 3: Fair credit score, much higher income requirement
eligible_for_loan(Applicant, Amount, Result) :-
    Credit >= 600,
    Credit < 650,
    Income >= Amount * 5,
    Result = conditional.

% Rule 4: Poor credit score
eligible_for_loan(Applicant, Amount, Result) :-
    Credit < 600,
    Result = denied.
