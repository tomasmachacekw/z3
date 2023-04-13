;; shared variable names
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(declare-const f Bool)

;; variables local to A
(declare-const au Bool)
(declare-const av Bool)
(declare-const aw Bool)
(declare-const ax Bool)
(declare-const ay Bool)
(declare-const az Bool)


;; variables local to B
(declare-const bu Bool)
(declare-const bv Bool)
(declare-const bw Bool)
(declare-const bx Bool)
(declare-const by Bool)
(declare-const bz Bool)


;; A and B sat cubes
;; A ^ B is sat
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) ax)
           ;; B
           (and b (not d) bz (not by))
           )

;; A and B sat cubes
;; A ^ B is unsat
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) d f ay)
           ;; B
           (and b (not d) bz (not by))
           )

;; A and B cubes
;; A is unsat (over shared vars)
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) d f c)
           ;; B
           (and b (not d) bz (not by))
           )

;; A and B cubes
;; A is unsat (over local vars)
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) az d f c (not az))
           ;; B
           (and b (not d) bz (not by))
           )


;; A and B cubes
;; B is unsat (over shared vars)
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) d f)
           ;; B
           (and b (not d) bz (not by) d)
           )

;; A and B cubes
;; B is unsat (over local vars)
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) d f)
           ;; B
           (and b by (not d) bz (not by) d)
           )
