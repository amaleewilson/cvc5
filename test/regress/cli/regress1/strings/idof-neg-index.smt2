(set-logic ALL)

(set-info :status unsat)
(declare-fun s () String)
(declare-fun x () Int)
(assert (< x 0))
(assert (>= (str.indexof s "goodbye" x) 0))
(check-sat)
