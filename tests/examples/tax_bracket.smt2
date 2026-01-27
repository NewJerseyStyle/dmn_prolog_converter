; Tax Bracket Determination
; Determines tax rate based on annual income

(declare-const Income Int)
(declare-const TaxRate Int)

; Rule 1: High income bracket (35% tax rate)
(assert (=> (>= Income 100000) (= TaxRate 35)))

; Rule 2: Upper-middle income bracket (28% tax rate)
(assert (=> (and (>= Income 50000) (< Income 100000)) (= TaxRate 28)))

; Rule 3: Middle income bracket (22% tax rate)
(assert (=> (and (>= Income 30000) (< Income 50000)) (= TaxRate 22)))

; Rule 4: Lower-middle income bracket (15% tax rate)
(assert (=> (and (>= Income 15000) (< Income 30000)) (= TaxRate 15)))

; Rule 5: Low income bracket (10% tax rate)
(assert (=> (< Income 15000) (= TaxRate 10)))

(check-sat)
(get-model)
