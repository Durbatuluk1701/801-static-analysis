(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

; Declare variables
(declare-sort Vars)
(declare-sort Lines)
(declare-fun EN (Lines (Pair Vars Lines)) Bool)
(declare-fun EX (Lines (Pair Vars Lines)) Bool)

(declare-fun ASGN (Vars Lines) Bool)
; ASGN v l -> (forall v' l'; v <> v' -> (EN l (v', l') = EX l (v', l')))
; ASGN v l -> (forall l'; l = l' <-> EX l (v, l'))
(assert 
  (forall ((v Vars) (l Lines))
    (implies 
      (ASGN v l)
      (
        and 
          (forall ((v2 Vars) (l2 Lines)) (implies (not (= v v2)) (iff (EN l (mk-pair v2 l2)) (EX l (mk-pair v2 l2)))))
          (forall ((l2 Lines)) (iff (= l l2) (EX l (mk-pair v l2))))
      )
    )
  )
)

(declare-fun NOT_ASGN (Lines) Bool)
; NOT_ASGN l -> (forall v2 l2, EN l (v2,l2) = EX l (v2,l2))
(assert 
  (forall ((l Lines))
    (implies
      (NOT_ASGN l)
      (forall ((val (Pair Vars Lines)))
        (= (EN l val) (EX l val))
      )
    )
  )
)

; CHECK ALL LINES COVERED: 
; (forall l, (exists v, ASGN v l) \/ (NOT_ASGN l))
(assert
  (forall ((l Lines))
    (xor
      (exists ((v Vars)) (ASGN v l))
      (NOT_ASGN l)
    )
  )
)

; FLOWS : Lines -> Lines -> Bool
; Flows l1 l2 -> 
(declare-fun Flows (Lines Lines) Bool)
(assert 
  (forall ((l1 Lines) (l2 Lines) (val (Pair Vars Lines)))
    (implies
      (Flows l1 l2)
      (implies
        (EX l1 val)
        (EN l2 val)
      )
    )
  )
)

;;;;;; Program Specific Stuff
(declare-const X Vars)
(declare-const Y Vars)
(declare-const Z Vars)
(assert (not (= X Y)))
(assert (not (= X Z)))
(assert (not (= Y Z)))
(declare-const l? Lines)
(declare-const l1 Lines)
(declare-const l2 Lines)
(declare-const l3 Lines)
(declare-const l4 Lines)
(declare-const l5 Lines)
(declare-const l6 Lines)
; 1: Y := X;
; 2: Z := 1;
; 3: while 1<Y do
; 4:   Z := Z * Y;
; 5:   Y := Y - 1;
; 6: Y := 0
;;;;;; Flows
(assert (Flows l1 l2))
(assert (Flows l2 l3))
(assert (Flows l3 l4))
(assert (Flows l4 l5))
(assert (Flows l5 l6))
(assert (Flows l5 l3))
;;;;;; ASGNs
;;;; Pre Conditions Asgns
(assert (ASGN Y l?))
(assert (ASGN X l?))
(assert (ASGN Z l?))
;;;; Program Asgns
(assert (ASGN Y l1))
(assert (ASGN Z l2))
(assert (NOT_ASGN l3))
(assert (ASGN Z l4))
(assert (ASGN Y l5))
(assert (ASGN Y l6))
(assert (not (= l2 l4)))

;;;;;;; Questions
; 1. X has not been initiatlized at the end of the program
(assert (forall ((l Lines)) (iff (EX l6 (mk-pair X l)) (= l l?))))
; 2. The assignment of Z at either label 2 and 4 may reach label 6
(assert (EN l6 (mk-pair Z l2))) 
(assert (EN l6 (mk-pair Z l4)))
; 3. The assignment of Z at label 2 does not reach label 5
(assert (not (EN l5 (mk-pair Z l2))))
; 4. There is no model where X has been assigned before program exit.
; Refer to 1.
(assert (not (exists ((l Lines)) (forall ((l_orig Lines)) (implies (not (= l_orig l?)) (EX l (mk-pair X l_orig)))))))


; Perform reaching analysis
(check-sat)
