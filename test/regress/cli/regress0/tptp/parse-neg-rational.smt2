(set-logic ALL)
(set-info :status unsat)
(declare-sort $$unsorted 0)
(assert (not (< (/ (- 1) 4) (/ 1 4))))
(set-info :filename parse-neg-rational)
(check-sat-assuming ( true ))