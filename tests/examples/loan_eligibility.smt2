; Loan Eligibility Decision
; Determines if an applicant is eligible for a loan based on credit score and income

(declare-const Credit Int)
(declare-const Income Int)
(declare-const Amount Int)
(declare-const Eligible Bool)

; Rule 1: High credit score, sufficient income
(assert (=> (and (>= Credit 700) (>= Income (* Amount 3))) (= Eligible true)))

; Rule 2: Good credit score, higher income requirement
(assert (=> (and (>= Credit 650) (< Credit 700) (>= Income (* Amount 4))) (= Eligible true)))

; Rule 3: Fair credit score, much higher income requirement
(assert (=> (and (>= Credit 600) (< Credit 650) (>= Income (* Amount 5))) (= Eligible false)))

; Rule 4: Poor credit score
(assert (=> (< Credit 600) (= Eligible false)))

(check-sat)
(get-model)
