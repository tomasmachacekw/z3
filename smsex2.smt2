(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(declare-const f Bool)

(satmodsat (a b c d)  (and  (or (not c) (not d)) (or (not c) d)) (and (or a b) (or (not a) c) (or (not b) c)))
(satmodsat (a b c d) (and (or a b) (or (not a) c) (or (not b) c)) (and  (or (not c) (not d)) (or (not c) d)))