(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(declare-const f Bool)
(declare-const x Bool)
(declare-const y Bool)


;; Example from Arie. -c is a good interpolant to learn but the
;; current implementation only learns -a || -b
;; ITP: (or (not b) (not a))
(satmodsat (a b c d)
	   (and (or (not a) (not b) c) (or (not f) (not c)) (or f (not c)))
	   (and a b))


;; Example where IC3 is much worse than SAT MOD SAT
;; abcdef encode php
;; ITP: (not x)
(satmodsat (x y a b c d e)
	   (and (or (not y) (not x)) (or y (not x)) (or (not a) (not c)) (or (not a) (not e)) (or (not c) (not e)) (or (not b) (not d)) (or (not b) (not f)) (or (not d) (not f)))
	   (and x (or a b) (or c d) (or e f)))

;; ITP: (and x)
(satmodsat (x y a b c d e)
	   (and x (or a b) (or c d) (or e f))
	   (and (or (not y) (not x)) (or y (not x)) (or (not a) (not c)) (or (not a) (not e)) (or (not c) (not e)) (or (not b) (not d)) (or (not b) (not f)) (or (not d) (not f))))

;; ITP: (and (or y x) (or (not y) x))
(satmodsat (x y a b c d e)
	   (and (or y x) (or (not y) x) (or a b) (or c d) (or e f))
	   (and (or (not y) (not x)) (or y (not x)) (or (not a) (not c)) (or (not a) (not e)) (or (not c) (not e)) (or (not b) (not d)) (or (not b) (not f)) (or (not d) (not f))))

;; ITP: (and (or (not y) (not x)) (or y (not x)))
(satmodsat (x y a b c d e)
	   (and (or (not y) (not x)) (or y (not x)) (or (not a) (not c)) (or (not a) (not e)) (or (not c) (not e)) (or (not b) (not d)) (or (not b) (not f)) (or (not d) (not f)))
       (and (or y x) (or (not y) x) (or a b) (or c d) (or e f)))

;; abcdef encode php
;; ITP: (not (and (or d c) (or b a) (or f e)))
(satmodsat (a b c d e f)
	   (and (or (not y) (not x)) (or y (not x))
	   	(or (not a) (not c))
		(or (not a) (not e))
		(or (not c) (not e))
		(or (not b) (not d))
		(or (not b) (not f))
		(or (not d) (not f)))
	   (and x (or a b)
		  (or c d)
		  (or e f)))
;; ITP: (not (and (or (not d) (not b))
                  ;; (or (not c) (not e))
                  ;; (or (not a) (not e))
                  ;; (or (not c) (not a))
                  ;; (or (not d) (not f))
                  ;; (or (not b) (not f))))
(satmodsat (a b c d e f)
	   (and x (or a b)
		      (or c d)
		      (or e f))

        (and (or (not y) (not x))
             (or y (not x))
	   	     (or (not a) (not c))
		     (or (not a) (not e))
		     (or (not c) (not e))
		     (or (not b) (not d))
		     (or (not b) (not f))
		     (or (not d) (not f))))
