; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :source |printed by MathSAT|)
(declare-fun X () Real)

(assert (let ((.def_44 (* (- (/ 11 10)) X)))
(let ((.def_45 (exp .def_44)))
(let ((.def_50 (* 250 .def_45)))
(let ((.def_40 (* (- (/ 13 10)) X)))
(let ((.def_41 (exp .def_40)))
(let ((.def_52 (* 173 .def_41)))
(let ((.def_53 (+ .def_52 .def_50)))
(let ((.def_54 (* 250 X)))
(let ((.def_55 (+ .def_54 .def_53)))
(let ((.def_56 (<= .def_55 (/ 595 2))))
(let ((.def_57 (not .def_56)))
(let ((.def_31 (<= 0 X)))
(let ((.def_32 (not .def_31)))
(let ((.def_58 (or .def_32 .def_57)))
(let ((.def_59 (not .def_58)))
.def_59))))))))))))))))
(check-sat)