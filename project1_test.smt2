; Declare boolean variables for each program point and each variable
(declare-fun X_1 () Bool)
(declare-fun Y_1 () Bool)
(declare-fun Z_1 () Bool)
(declare-fun X_2 () Bool)
(declare-fun Y_2 () Bool)
(declare-fun Z_2 () Bool)
(declare-fun X_3 () Bool)
(declare-fun Y_3 () Bool)
(declare-fun Z_3 () Bool)
(declare-fun X_4 () Bool)
(declare-fun Y_4 () Bool)
(declare-fun Z_4 () Bool)
(declare-fun X_5 () Bool)
(declare-fun Y_5 () Bool)
(declare-fun Z_5 () Bool)
(declare-fun X_6 () Bool)
(declare-fun Y_6 () Bool)
(declare-fun Z_6 () Bool)

; Initial constraints
(assert X_1)
(assert (not Y_1))
(assert (not Z_1))

; Transfer functions
(assert (=> X_1 Y_2))      ; 1: Y := X;
(assert (not Y_2))          ; 2: Z := 1;
(assert (and Y_2 X_3))     ; 3: while 1<Y do
(assert (or (and X_3 Y_4) (and (not X_3) Z_3)))  ; 4:   Z := Z * Y;
(assert (and (or (and X_3 Y_4) (and (not X_3) Z_3)) Y_5))  ; 5:   Y := Y - 1;
(assert (and (not X_3) (not Y_5) (not Z_3))) ; 6: Y := 0

; Final constraints
(assert (and (not X_3) (not Y_5) (not Z_3)))

; Check satisfiability
(check-sat)
