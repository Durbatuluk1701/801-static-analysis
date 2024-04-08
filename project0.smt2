(declare-const a Bool)
(declare-const b Bool)
(declare-const f Bool)
(declare-const g Bool)
(declare-const h Bool)
(assert 
	(not 
		(= 
			(or (and a f) (and (not a) (or (and b g) (and (not b) h))))
			(or 
				(and 
					(and (not a) (not b)) 
					h
				) 
				(and 
					(not (and (not a) (not b))) 
					(or (and (not a) g) (and a f))
				)
			)
		)
	)
)
(check-sat)
