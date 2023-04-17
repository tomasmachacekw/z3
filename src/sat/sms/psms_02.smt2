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

(declare-const a1 Bool)
(declare-const a2 Bool)
(declare-const a3 Bool)
(declare-const a4 Bool)
(declare-const a5 Bool)
(declare-const a6 Bool)


;; variables local to B
(declare-const bu Bool)
(declare-const bv Bool)
(declare-const bw Bool)
(declare-const bx Bool)
(declare-const by Bool)
(declare-const bz Bool)

(declare-const b1 Bool)
(declare-const b2 Bool)
(declare-const b3 Bool)
(declare-const b4 Bool)
(declare-const b5 Bool)
(declare-const b6 Bool)

;; A is a cube
;; B is not a cube but fully is assigned after unit literals + BCP
;; A ^ B is sat
(satmodsat (a b c d) ;; vars
           ;; A
           (and a (not c) ax)
           ;; B
           (and b (not d) bz (not by)
                (or (not b) c bx))
           )

;; A is a cube
;; B is not a cube and not fully is assigned after BCP, but no conflicts should be found
;; A ^ B is sat
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) ax)
           ;; B
           (and b (not d) bz (not by)
                (or (not b) c bx)
                (or bu (not bw))
                (or bu bv)
           ))

;; A is a cube
;; B is not a cube and not fully is assigned after BCP, and learning may be required
;; A ^ B is sat
(satmodsat (a b c d) ;; vars
           ;;
           (and a b (not c) ax)
           ;; B
           (and b (not d) bz (not by)
                (or (not b) c bx)
                (or bu (not bw) bv)
                (or bu bw bv)
                (or (not bw) (not bv))
           ))


;; A is a cube
;; B is not a cube but fully is assigned after BCP, binary clauses
;; A ^ B is unsat
(satmodsat (a b c d) ;; vars
           ;; A
           (and a ax)
           ;; B
           (and (not d)
                (or (not a) (not bx))
                (or bx (not bz))
                (or bz d))
           )
;; expected: not a


;; A is a cube
;; B is not a cube but fully is assigned after BCP
;; A ^ B is unsat
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) d ax)
           ;; B
           (and (not d) bz (not by)
                (or (not a) (not bx) (not b))
                (or bx a (not bz)))
           )
;; expected: not a || not b


;; A is a cube
;; B is not a cube but fully is assigned after BCP (two unsat cores)
;; A ^ B is unsat
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) ax)
           ;; B
           (and (not d) bz bw
                (or (not a) (not bx) (not b))
                (or bx a (not bz))
                (or (not bu) (not a) (not bw))
                (or bu d c))
           )
;; expected: not a || not b
;;      opt: (c && d) --> not a


;; A is a cube
;; B is not a cube and not fully is assigned after BCP, learning required
;; A ^ B is unsat
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) ax (not d))
           ;; B
           (and
                (or d bx b)
                (or (not bx) (not b) d)
                (or (not b) d a)       ;; b --> a (with d to not have it binary)
                (or (not b) d (not a)) ;; b --> not a
                (or d b)
                ;; useless clauses
                (or bx by)
                (or by a b1))
           )


;; A is a cube
;; B is not a cube and unsat but learning required
(satmodsat (a b c d) ;; vars
           ;; A
           (and a b (not c) ax)
           ;; B
           (and (not d)
                (or d bx b)
                (or (not bx) (not b) d)
                (or (not b) d a)       ;; b --> a (with d to not have it binary)
                (or (not b) d (not a)) ;; b --> not a
                (or d b)
                ;; useless clauses
                (or bx by)
                (or by a b1))
           )
;; expected: false?
