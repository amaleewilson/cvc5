; EXPECT: unknown
(set-logic UFDT)
(declare-sort B 0)
(declare-sort b 0)
(declare-sort o 0)
(declare-sort _b 0)
(declare-datatypes ((B_ 0) (C 0) (A 0) (A_ 0) (A_b 0) (a 0) (b_ 0) (_a 0) (_b_ 0) (b_a 0) (b_b 0) (A_b_ 0) (_b_b 0) (a_ 0) (B_a 0) (a_b 0) (r 0) (A_b_b 0) (l 0) (_l 0)) (((oc) (s (h B))) ((r) (b)) ((e)) ((p)) ((i)) ((p)) ((m)) ((e)) ((p)) ((i)) ((m)) ((a)) ((n)) ((m)) ((n)) ((s)) ((n)) ((n)) ((n)) ((n))))
(declare-fun v () B)
(declare-fun u () b)
(declare-fun f (b B) Bool)
(declare-fun f (o B_) Bool)
(declare-fun f (_b b) o)
(declare-fun c (Bool) _b)
(assert (forall ((v2 B)) (= v2 v)))
(assert (forall ((? C)) (or (= ? r) (= ? b))))
(assert (forall ((? o)) (or (f ? oc) (f ? (s v)))))
(assert (forall ((? o)) (= (f ? oc) (forall ((?v B_)) (f ? ?v)))))
(assert (forall ((?v b) (v2 B_)) (= (f (f (c false) ?v) v2) (ite (= v2 oc) false (f ?v (h v2))))))
(assert (forall ((?v B_)) (f u (h oc))))
(check-sat)