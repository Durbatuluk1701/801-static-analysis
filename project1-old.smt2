(set-option :produce-unsat-cores true) ; enable generation of unsat cores
;(set-option :produce-proofs true)
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

; Declare variables
(declare-datatypes () ((Vars X Y Z)))
(declare-datatypes () ((Lines l? l1 l2 l3 l4 l5 l6)))
(declare-fun EN (Lines (Pair Vars Lines)) Bool)
(declare-fun EX (Lines (Pair Vars Lines)) Bool)

(declare-fun ASGN (Vars Lines) Bool)
; ASGN v l -> (forall v' l'; v <> v' -> (EN l (v', l') = EX l (v', l')))
; ASGN v l -> (forall l'; l = l' <-> EX l (v, l'))
(assert 
  (forall ((v Vars) (l Lines))
    (implies 
      (ASGN v l)
      (forall ((v2 Vars) (l_2 Lines)) (iff (not (= v v2)) (= (EN l (mk-pair v2 l_2)) (EX l (mk-pair v2 l_2)))))
    )
  )
)

(assert
  (forall ((v Vars) (l Lines))
    (iff
      (ASGN v l)
      (forall ((l_2 Lines)) (iff (= l l_2) (EX l (mk-pair v l_2))))
    )
  )
)

;(assert
;  (forall ((v Vars) (li Lines))
;    (implies
;      (not (ASGN v li))
;      (forall ((l_prev Lines)) (= (EN li (mk-pair v l_prev)) (EX li (mk-pair v l_prev))))
;    )
;  )
;)

(assert
  (forall ((v Vars) (l_prev Lines))
    (implies
      (not (ASGN v l_prev))
      (forall ((l_curr Lines)) (not (or (EN l_curr (mk-pair v l_prev)) (EX l_curr (mk-pair v l_prev)))))
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
    (and
      (iff
        (exists ((v Vars)) (ASGN v l))
        (not (NOT_ASGN l))
      )
      (iff
        (NOT_ASGN l)
        (forall ((v Vars)) (not (ASGN v l)))
      )
    )
  )
)

; FLOWS : Lines -> Lines -> Bool
; Flows l1 l2 -> 
(declare-fun Flows (Lines Lines) Bool)
;(assert 
;  (forall ((l1 Lines) (l2 Lines) (val (Pair Vars Lines)))
;    (implies
;      (Flows l1 l2)
;      (implies
;        (EX l1 val)
;        (EN l2 val)
;      )
;    )
;  )
;)

(assert 
  (forall ((l_1 Lines) (l_2 Lines))
    (implies (not (= l_1 l_2))
      (iff
        (Flows l_1 l_2)
        (forall ((val (Pair Vars Lines)))
          (implies
            (EX l_1 val)
            (EN l_2 val)
          )
        )
      )
    )
  )
)

; 1: Y := X;
; 2: Z := 1;
; 3: while 1<Y do
; 4:   Z := Z * Y;
; 5:   Y := Y - 1;
; 6: Y := 0
;;;;;; Flows
(assert (forall ((l Lines)) (iff (= l l1) (Flows l? l))))
(assert (forall ((l Lines)) (iff (= l l2) (Flows l1 l))))
(assert (forall ((l Lines)) (iff (= l l3) (Flows l2 l))))
(assert (forall ((l Lines)) (iff (or (= l l4) (= l l6)) (Flows l3 l))))
(assert (forall ((l Lines)) (iff (= l l5) (Flows l4 l))))
(assert (forall ((l Lines)) (iff (or (= l l6) (= l l3)) (Flows l5 l))))
(assert (forall ((l Lines)) (not (Flows l6 l))))
;;;;;; ASGNs
;;;; Pre Conditions Asgns
(assert (and (ASGN Y l?) (ASGN X l?) (ASGN Z l?)))
;;;; Program Asgns
(assert (ASGN Y l1))
(assert (ASGN Z l2))
(assert (NOT_ASGN l3))
;(assert (forall ((val (Pair Vars Lines))) (= (EN l3 val) (EX l3 val))))
(assert (ASGN Z l4))
(assert (ASGN Y l5))
(assert (ASGN Y l6))
(check-sat)
;;;;;;; Questions
; 1. X has not been initiatlized at the end of the program
(echo "Q1")
(assert (forall ((l Lines)) (iff (EX l6 (mk-pair X l)) (= l l?))))
(check-sat)
; 2. The assignment of Z at either label 2 and 4 may reach label 6
(echo "Q2")
(assert (forall ((v Vars) (l Lines)) (and (iff (= l l?) (EN l1 (mk-pair v l))))))
(assert (forall ((l Lines)) (iff (not (= l l?)) (not (EX l1 (mk-pair X l))))))
(assert (forall ((l Lines)) (iff (not (= l l?)) (not (EX l1 (mk-pair Z l))))))
(assert (forall ((l Lines)) (iff (= l l1) (EX l1 (mk-pair Y l)))))
(assert (EX l1 (mk-pair X l?)))
(assert (EX l1 (mk-pair Z l?)))
(assert (not (EX l1 (mk-pair Y l?))))

(assert (forall ((l Lines)) (iff (= l l?) (EN l2 (mk-pair X l)))))
(assert (forall ((l Lines)) (iff (= l l?) (EN l2 (mk-pair Z l)))))
(assert (forall ((l Lines)) (iff (= l l1) (EN l2 (mk-pair Y l)))))
(assert (forall ((l Lines)) (iff (= l l?) (EX l2 (mk-pair X l)))))
(assert (forall ((l Lines)) (iff (= l l1) (EX l2 (mk-pair Y l)))))
(assert (forall ((l Lines)) (iff (= l l2) (EX l2 (mk-pair Z l)))))

(assert (forall ((val (Pair Vars Lines))) (implies (EX l2 val) (EN l3 val))))
;(assert (forall ((v Vars)) (iff (= v X) (EN l3 (mk-pair v l?)))))
(assert (forall ((val (Pair Vars Lines))) (= (EN l3 val) (EX l3 val))))

;(assert (forall ((v Vars)) (iff (= v X) (EN l4 (mk-pair v l?)))))
;(assert (forall ((v Vars)) (iff (= v X) (EX l4 (mk-pair v l?)))))
;(assert (forall ((v Vars)) (iff (= v X) (EN l5 (mk-pair v l?)))))
;(assert (forall ((v Vars)) (iff (= v X) (EX l5 (mk-pair v l?)))))

(assert (EX l5 (mk-pair Z l?)))

;(assert (not (EN l6 (mk-pair Z l?))))
;(assert (EN l6 (mk-pair Z l?))) 
;(assert (EN l6 (mk-pair Z l2)))
;(assert (EN l6 (mk-pair Z l4)))
(check-sat)
; 3. The assignment of Z at label 2 does not reach label 5
(echo "Q3")
;(assert (not (EN l5 (mk-pair Z l2))))
(assert (forall ((l Lines)) (iff (not (= l l4)) (not (EN l5 (mk-pair Z l))))))
(assert (EN l5 (mk-pair Y l?)))
(check-sat)
; 4. There is no model where X has been assigned before program exit.
; Refer to 1.
(echo "Q4")
;(assert (not (exists ((l Lines)) (forall ((l_orig Lines)) (implies (not (= l_orig l?)) (EX l (mk-pair X l_orig)))))))
;(assert (forall ((l Lines)) (EX l (mk-pair X l?))))
;(assert (forall ((l Lines) (l_orig Lines)) (iff (= l_orig l?) (EX l (mk-pair X l_orig)))))
(check-sat)
