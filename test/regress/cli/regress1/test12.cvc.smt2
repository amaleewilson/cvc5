; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-sort A 0)
(declare-fun P_1 () Bool)
(declare-fun P_2 () Bool)
(declare-fun P_3 () Bool)
(assert (or (or (not P_1) P_2) P_2))
(assert (or (or (not P_1) P_2) P_3))
(declare-fun P_4 () Bool)
(declare-fun P_5 () Bool)
(assert (or (or (not P_1) (not P_4)) P_2))
(assert (or (or (not P_1) (not P_5)) P_2))
(declare-fun P_6 () Bool)
(declare-fun P_7 () Bool)
(assert (or (or (not P_2) P_6) P_1))
(assert (or (or (not P_2) P_7) P_1))
(declare-fun P_8 () Bool)
(declare-fun P_9 () Bool)
(assert (or (or (not P_2) (not P_8)) P_1))
(assert (or (or (not P_2) (not P_9)) P_1))
(declare-fun P_10 () Bool)
(assert (or (or P_2 P_1) P_4))
(assert (or (or P_2 P_1) P_10))
(assert (or (or (not P_2) (not P_1)) P_4))
(assert (or (or (not P_2) (not P_1)) P_10))
(declare-fun P_11 () Bool)
(assert (or (or (not P_6) P_2) P_1))
(assert (or (or (not P_11) P_2) P_1))
(assert (or (or (not P_6) (not P_2)) (not P_1)))
(assert (or (or (not P_11) (not P_2)) (not P_1)))
(push 1)
(check-sat-assuming ( (not (or (not P_2) (not P_3))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_1 (not P_3))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or (not P_2) P_1)) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_5 (not P_2))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_1 (not P_2))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_5 P_1)) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or (not P_7) (not P_1))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_2 (not P_1))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not P_2) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_9 (not P_1))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_2 (not P_1))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not P_2) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or (not P_1) (not P_10))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or (not P_2) (not P_10))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or (not P_1) (not P_2))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_1 (not P_10))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_2 (not P_10))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_1 P_2)) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or (not P_2) (not P_1))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_11 (not P_1))) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or (not P_2) P_11)) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_2 P_1)) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_11 P_1)) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not (or P_2 P_11)) ))
(pop 1)
(declare-fun P_12 () Bool)
(assert (or (not P_12) P_2))
(assert (or (not P_12) P_3))
(assert (or (or P_12 (not P_1)) P_2))
(assert (or (or P_12 (not P_1)) P_2))
(declare-fun P_13 () Bool)
(assert (or (not P_13) (not P_4)))
(assert (or (not P_13) (not P_5)))
(assert (or (or P_13 (not P_1)) P_2))
(assert (or (or P_13 (not P_1)) P_2))
(assert (or (not P_2) P_1))
(assert (or (not P_2) P_1))
(assert (or (not P_2) P_1))
(assert (or (not P_2) P_1))
(declare-fun P_14 () Bool)
(assert (or (or P_14 P_2) P_1))
(assert (or (or P_14 P_2) P_1))
(assert (or (not P_14) P_4))
(assert (or (not P_14) P_10))
(assert (or (or P_14 (not P_2)) (not P_1)))
(assert (or (or P_14 (not P_2)) (not P_1)))
(declare-fun P_15 () Bool)
(assert (or (or P_15 P_2) P_1))
(assert (or (or P_15 P_2) P_1))
(assert (or (not P_15) (not P_6)))
(assert (or (not P_15) (not P_11)))
(assert (or (or P_15 (not P_2)) (not P_1)))
(assert (or (or P_15 (not P_2)) (not P_1)))
(push 1)
(check-sat-assuming ( (not (not P_3)) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not P_12) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not P_11) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not P_15) ))
(pop 1)
(assert (not P_15))
(assert (not P_15))
(push 1)
(check-sat-assuming ( (not (not P_10)) ))
(pop 1)
(push 1)
(check-sat-assuming ( (not false) ))