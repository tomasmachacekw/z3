;; assume(x = y);
;; if (*) { c = f(z); d = f(w) }
;; else { c = f(x); d = f(y) }
;; if (*) { a = f(z); b = f(w) }
;; else { a = f(x); b = f(y) }
;; while (*) {
;;    assume (z = w);
;;    if (*) { x = g(a); y = g(b); }
;;    else { x  = f(c); y = f(d); }
;;    a, b, c, d, x, y, w, z = m(a), m(b), m(c), m(d), m(x), m(y), m(w), m(z);
;; }
;; assert(x = y);

(set-logic HORN)
(declare-fun inv ( (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int Int  Int Int Int Int ) Bool)

(assert
  (forall ( (cond Bool) (f (Array Int Int)) (g (Array Int Int)) (m (Array Int Int)) (x Int) (y Int) (w Int) (z Int) (a Int) (b  Int) (c Int) (d Int) ) 
    (=>
      (and
        (= x y)
	(= c (ite cond (f z) (f x)))
	(= d (ite cond (f w) (f y)))
	(= a (ite cond (f z) (f x)))
	(= b (ite cond (f w) (f y)))
      )
      (inv f g m w x y z a b c d)
    )
  )
)

(assert
  (forall ( (cond Bool) (f (Array Int Int)) (g (Array Int Int)) (m (Array Int Int)) (x Int) (y Int) (w Int) (z Int) (a Int) (b  Int) (c Int) (d Int)
  	    	  	   	      	       	      	  	   	      	    (xp Int) (yp Int) (xpp Int) (ypp Int) (wp Int) (zp Int) (ap Int) (bp  Int) (cp Int) (dp Int)) 
    (=>
      (and
	(inv f g m w x y z a b c d)
	(= z w)	
	(= xp (ite cond (f a) (f c)))
	(= yp (ite cond (f b) (f d)))
	(= wp (m w))
	(= xpp (m xp))
	(= ypp (m yp))
	(= zp (m z))
	(= ap (m a))
	(= bp (m b))
	(= cp (m c))
	(= dp (m d))
      )
      (inv f g m wp xpp ypp zp ap bp cp dp)
    )
  )
)


(assert
  (forall ( (cond Bool) (f (Array Int Int)) (g (Array Int Int)) (m (Array Int Int)) (x Int) (y Int) (w Int) (z Int) (a Int) (b  Int) (c Int) (d Int) ) 
    (=>
      (and
      (inv f g m w x y z a b c d)
      (not (= x y))
      )
      false
    )
  )
)

(check-sat)
(get-model)
(exit)
