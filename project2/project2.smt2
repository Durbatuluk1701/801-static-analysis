(declare-datatypes () ((Vars X Y Z)))
(declare-datatypes () ((Lines l? l1 l2 l3 l4 l5 l6 l7)))

(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

(declare-fun EN (Lines (Pair Vars Lines)) Bool)
(declare-fun EX (Lines (Pair Vars Lines)) Bool)

(define-fun ASGN ((v Vars) (l Lines)) Bool
; ASGN v l -> (forall v' l'; v <> v' -> (EN l (v', l') = EX l (v', l')))
; ASGN v l -> (forall l'; l = l' <-> EX l (v, l'))
  (forall ((l_3 Lines)) 
    (iff (= l l_3) (EX l (mk-pair v l_3)))
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

(define-fun NOT_ASGN ((l Lines)) Bool
; NOT_ASGN l -> (forall v2 l2, EN l (v2,l2) = EX l (v2,l2))
  (forall ((v Vars)) (not (ASGN v l)))
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
(assert (forall ((l Lines)) (iff (= l l1) (Flows l? l))))
(assert (forall ((v Vars)) (= (= v Y) (ASGN v l1))))
(assert (forall ((l Lines)) (iff (= l l2) (Flows l1 l))))
(assert (forall ((v Vars)) (= (= v Z) (ASGN v l2))))
(assert (forall ((l Lines)) (iff (= l l3) (Flows l2 l))))
(assert (NOT_ASGN l3))
(assert (forall ((l Lines)) (iff (or (= l l4) (= l l6)) (Flows l3 l))))
(assert (forall ((v Vars)) (= (= v Z) (ASGN v l4))))
(assert (forall ((l Lines)) (iff (= l l5) (Flows l4 l))))
(assert (forall ((v Vars)) (= (= v Y) (ASGN v l5))))
(assert (forall ((l Lines)) (iff (or (= l l3) (= l l6)) (Flows l5 l))))
(assert (NOT_ASGN l6))
(assert (forall ((l Lines)) (iff (= l l7) (Flows l6 l))))
(assert (forall ((v Vars)) (= (= v Y) (ASGN v l7))))
(assert (forall ((l Lines)) (not (Flows l7 l))))
(check-sat)
(get-model)