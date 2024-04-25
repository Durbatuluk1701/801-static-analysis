(set-option :produce-unsat-cores true)
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

; Declare variables
(declare-datatypes () ((Vars X Y Z)))
(declare-datatypes () ((Lines l? l1 l2 l3 l4 l5 l6)))
(declare-fun EN (Lines (Pair Vars Lines)) Bool)
(declare-fun EX (Lines (Pair Vars Lines)) Bool)

(define-fun ASGN ((v Vars) (l Lines)) Bool
; ASGN v l -> (forall v' l'; v <> v' -> (EN l (v', l') = EX l (v', l')))
; ASGN v l -> (forall l'; l = l' <-> EX l (v, l'))
  (=> 
    (not (= l l?))
    (forall ((v2 Vars) (l_3 Lines)) 
      (ite 
        (= v v2)
        (iff (= l l_3) (EX l (mk-pair v2 l_3)))
        (iff (EN l (mk-pair v2 l_3)) (EX l (mk-pair v2 l_3)))
      )
    )
  )
)

(define-fun NOT_ASGN ((l Lines)) Bool
; NOT_ASGN l -> (forall v2 l2, EN l (v2,l2) = EX l (v2,l2))
  (implies (not (= l l?))
    (and
      ;(forall ((val (Pair Vars Lines))) (= (EN l val) (EX l val)))
      (forall ((v Vars)) (not (ASGN v l)))
    )
  )
)

(assert
  (forall ((l_1 Lines) (v Vars))
    (or
      (ASGN v l_1)
      (forall ((l_2 Lines)) (= (EN l_1 (mk-pair v l_2)) (EX l_1 (mk-pair v l_2))))
    )
  )
)

(declare-fun Flows (Lines Lines) Bool)
(assert
  (forall ((l_1 Lines) (l_2 Lines))
    (implies
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

; Flowchains describes what it means to chain multiple flows assertions together
; e.g. if l1 flows to l2 and l2 flows to l3, then l1 flowchains to l3
; this allows us to make a restriction that if a line claims to have access to a variable from a different line,
; then that other line must flowchain and have an assignment
; e.g. if l3 claims to have access to v from l1, then it must be that l1 flowchains to l3 and l1 assigns v
; note/todo: it is possible this analysis is currently technically too broad,
; because it technically still allows Z3 to say l3 has v from l1 even if l2 comes between them and also assigns v
; however, it is also possible that other assertions made elsewhere make this impossible
; realistically, this is only being used to prevent Z3 from making an arbitrary assignment in a loop, which can be self-fulfilling due to flows analysis
(declare-fun Flowchains (Lines Lines) Bool)
; Flows -> Flowchains
(assert
  (forall ((l_1 Lines) (l_2 Lines))
    (=> (Flows l_1 l_2) (Flowchains l_1 l_2))
  )
)
; Flowchains l1 l2 /\ Flowchains l2 l3 <-> Flowchains l1 l3
(assert
  (forall ((l_1 Lines) (l_2 Lines) (l_3 Lines))
    (= (and (Flowchains l_1 l_2) (Flowchains l_2 l_3)) (Flowchains l_1 l_3))
  )
)
; l1 entry has v from l2 -> ASGN v l2 /\ Flowchains l2 l1
; not <->, because l2 may assign a var and chain into l1, but a distinct l3 may overwrite the assignment
(assert
  (forall ((l_1 Lines) (v Vars) (l_2 Lines))
    (=> (EN l_1 (mk-pair v l_2)) (and (ASGN v l_2) (Flowchains l_2 l_1)))
  )
)

; EN l1 has val <-> exists l2 where EX l2 val /\ flows l2 l1
; this is a distinct statement from the above Flowchains assertions, and should prevent the case
; where l3 has access to v from l1 even though l2 should be an overwriting assignment for v before l3
(assert
  (forall ((l_1 Lines) (val (Pair Vars Lines)))
    (=
      (and (not (= l_1 l?)) (EN l_1 val))
      (exists ((l_2 Lines)) (and (EX l_2 val) (Flows l_2 l_1)))
    ) 
  )
)

; if EX l != EN l for v then ASGN v l
(assert
  (forall ((l_1 Lines) (v Vars))
    (implies ;iff doesn't make sense (e.g. l?)
      (forall ((l_2 Lines)) (not (= (EX l_1 (mk-pair v l_2)) (EN l_1 (mk-pair v l_2)))))
      (ASGN v l_1)
    )
  )
)

;;;;;;;;;; l? Specific Information ;;;;;;;;;;
(assert (forall ((v Vars)) (ASGN v l?)))
(assert (forall ((v Vars) (l Lines)) (= (= l l?) (EN l? (mk-pair v l)))))
(assert (forall ((v Vars) (l Lines)) (= (= l l?) (EX l? (mk-pair v l)))))

(check-sat)

;;;;;;;;;;; Start Program Specific Configuration ;;;;;;;;;;;
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
(assert (forall ((l Lines)) (iff (or (= l l2) (= l l5)) (Flows l l3))))
(assert (forall ((l Lines)) (iff (= l l5) (Flows l4 l))))
(assert (forall ((l Lines)) (iff (or (= l l6) (= l l3)) (Flows l5 l))))
(assert (forall ((l Lines)) (not (Flows l6 l))))
(assert (forall ((l_1 Lines) (l_2 Lines)) (implies (Flows l_1 l_2) (not (= l_1 l_2)))))
;;;;;; ASGNs
;;;; Pre Conditions Asgns
; (assert (forall ((v Vars) (l Lines)) (= (= l l?) (EN l1 (mk-pair v l)))))
; (assert (forall ((v Vars) (l Lines)) (implies (not (= v Y)) (= (= l l?) (EX l1 (mk-pair v l))))))
; ;;;; Program Asgns
(assert (forall ((v Vars)) (= (= v Y) (ASGN v l1))))
(assert (forall ((v Vars)) (= (= v Z) (ASGN v l2))))
(assert (NOT_ASGN l3))
(assert (forall ((v Vars)) (= (= v Z) (ASGN v l4))))
(assert (forall ((v Vars)) (= (= v Y) (ASGN v l5))))
(assert (forall ((v Vars)) (= (= v Y) (ASGN v l6))))
(check-sat)

;;;;;;; Questions
; simple test setup to make sure there is a satisfying model
(push)
; Q1
(assert (forall ((l Lines)) (= (= l l?) (EX l6 (mk-pair X l)))))
(check-sat)
; Q2
(assert (forall ((l Lines)) (= (or (= l l2) (= l l4)) (EN l6 (mk-pair Z l)))))
; Q3
(assert (not (EN l5 (mk-pair Z l2))))
(assert (forall ((l Lines)) (iff (not (= l l4)) (not (EN l5 (mk-pair Z l))))))
;(assert (EN l5 (mk-pair Y l?)))
; Q4
(assert (not (exists ((l Lines)) (forall ((l_orig Lines)) (implies (not (= l_orig l?)) (EX l (mk-pair X l_orig)))))))
(assert (forall ((l Lines)) (EX l (mk-pair X l?))))
(assert (forall ((l Lines) (l_orig Lines)) (iff (= l_orig l?) (EX l (mk-pair X l_orig)))))
(check-sat)
(pop)

(echo "")
(echo "For the following questions, unsat means there are no violating models")
(echo "")

(echo "Q1: X has not been initialized at the end of the program")
(push)
(assert (exists ((l Lines)) (and (not (= l l?)) (EX l6 (mk-pair X l)))))
(check-sat)
(pop)
(echo "")

(echo "Q2: The assignment of Z at labels 2 and 4 may reach label 6")
(echo "The only assignments of Z that can reach label 6 are at labels 2 and 4")
(push)
(assert
  (exists ((l Lines))
    (= (not (or (= l l2) (= l l4))) (EN l6 (mk-pair Z l)))
  )
)
(check-sat)
(pop)
(echo "The assignment of Z at label 2 must reach label 6")
(push)
(assert (not (EN l6 (mk-pair Z l2))))
(check-sat)
(pop)
(echo "The assignment of Z at label 4 must reach label 6")
(push)
(assert (not (EN l6 (mk-pair Z l4))))
(check-sat)
(pop)

(echo "")
(echo "Q3: The assignment of Z at label 2 does not reach label 5")
(push)
(assert (EN l5 (mk-pair Z l2)))
(check-sat)
(pop)
(echo "")

(echo "Q4: There is no model where X has been assigned before program exit") ; Refer to 1?
(push)
(assert (exists ((l Lines) (l_orig Lines)) (and (not (= l_orig l?)) (or (EN l (mk-pair X l_orig)) (EX l (mk-pair X l_orig))))))
(check-sat)
(pop)
(echo "")
 