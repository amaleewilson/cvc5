; COMMAND-LINE: --dt-stc-ind
; EXPECT: unsat
(set-logic UFDT)
(declare-datatype Nat ((succ (pred Nat)) (zero)))
(declare-datatype Lst ((cons (head Nat) (tail Lst)) (nil)))
(declare-datatype Heap ((hleaf) (heap (rk Nat) (value Nat) (hleft Heap) (hright Heap))))
(declare-fun leq (Nat Nat) Bool)
(declare-fun rightHeight (Heap) Nat)
(assert (= (rightHeight hleaf) zero))
(assert (forall ((k Nat) (v Nat) (l Heap) (r Heap)) (= (rightHeight (heap k v l r)) (succ (rightHeight r)))))
(declare-fun hasLeftistProperty (Heap) Bool)
(assert (hasLeftistProperty hleaf))
(assert
 (forall ((k Nat) (v Nat) (l Heap) (r Heap))
   (= (hasLeftistProperty (heap k v l r))
      (and (hasLeftistProperty l)
           (hasLeftistProperty r)
           (leq (rightHeight r) (rightHeight l))
           (= k (succ (rightHeight r)))))))
(declare-fun merge (Heap Heap) Heap)
(declare-fun hinsert (Heap Nat) Heap)
(declare-fun hinsert-all (Lst Heap) Heap)
(assert (forall ((h Heap)) (= (hinsert-all nil h) h)))
(assert (forall ((h Heap) (n Nat) (l Lst)) (= (hinsert-all (cons n l) h) (hinsert (hinsert-all l h) n))))
(assert (forall ((x Heap) (n Nat)) (=> (hasLeftistProperty x) (hasLeftistProperty (hinsert x n)))))
(assert (not (forall ((n Lst) (x Heap)) (=> (hasLeftistProperty x) (hasLeftistProperty (hinsert-all n x))))))
(check-sat)