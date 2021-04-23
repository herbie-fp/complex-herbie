#lang racket

(require math/flonum math/bigfloat herbie/plugin "bigcomplex.rkt")

(eprintf "Loading complex number support...\n")

(define-type complex (complex? bigcomplex?)
  complex->bigcomplex
  bigcomplex->complex)

(define (complex-nan? x)
  (or (nan? (real-part x)) (nan? (imag-part x))))

(define (complex-inf? x)
  (or (infinite? (real-part x)) (infinite? (imag-part x))))

(define-representation (complex complex complex?)
  (λ (x) (make-rectangular (bigfloat->flonum (bigcomplex-re x)) (bigfloat->flonum (bigcomplex-im x))))
  (λ (x) (bigcomplex (bf (real-part x)) (bf (imag-part x))))
  (λ (x) (make-rectangular (ordinal->flonum (quotient x (expt 2 64))) (ordinal->flonum (modulo x (expt 2 64)))))
  (λ (x) (+ (* (expt 2 64) (flonum->ordinal (real-part x))) (flonum->ordinal (imag-part x))))
  128
  ;; TODO(interface): note that these values for special-values are incorrect;
  ;; any value that includes +nan.0 should be a special value, but because
  ;; types and representations are not cleanly separated, this is not reasonable to
  ;; express. Once types and representations are separated, fix this.
  (disjoin complex-nan? complex-inf?))

;; Abstract complex constants and ops

(define-constant I
  [bf (λ () (bigcomplex 0.bf 1.bf))]
  [nonffi (const 0+1i)]
  [ival #f])

(define-operator complex
  [bf bigcomplex] [ival #f] [nonffi make-rectangular])

(define-operator re
  [bf bigcomplex-re] [ival #f] [nonffi real-part])

(define-operator im
  [bf bigcomplex-im] [ival #f] [nonffi imag-part])

(define-operator conj
  [bf bf-complex-conjugate] [ival #f] [nonffi conjugate])

;; Implementations

(define-constant-impl (I I) complex
  [fl (const 0+1i)])

(define-operator-impl (+ +.c complex complex) complex
  [fl +] [bf bf-complex-add] [ival #f])

(define-operator-impl (- neg.c complex) complex
  [fl -] [bf bf-complex-neg] [ival #f])

(define-operator-impl (- -.c complex complex) complex
  [fl -] [bf bf-complex-sub] [ival #f])

(define-operator-impl (* *.c complex complex) complex
  [fl *] [bf bf-complex-mult] [ival #f])

(define-operator-impl (/ /.c complex complex) complex
  [fl /] [bf bf-complex-div] [ival #f])

(define-operator-impl (exp exp.c complex) complex
  [fl exp] [bf bf-complex-exp] [ival #f])

(define-operator-impl (log log.c complex) complex
  [fl log] [bf bf-complex-log] [ival #f])

(define-operator-impl (pow pow.c complex complex) complex
  [fl expt] [bf bf-complex-pow] [ival #f])

(define-operator-impl (sqrt sqrt.c complex) complex
  [fl sqrt] [bf bf-complex-sqrt] [ival #f])

(define-operator-impl (complex complex binary64 binary64) complex
  [fl make-rectangular])

(define-operator-impl (re re complex) binary64
  [fl real-part])

(define-operator-impl (im im complex) binary64
  [fl imag-part])

(define-operator-impl (conj conj complex) complex
  [fl conjugate])

(define-ruleset commutativity.c (arithmetic simplify fp-safe complex)
  #:type ([a complex] [b complex])
  [+.c-commutative     (+.c a b)               (+.c b a)]
  [*.c-commutative     (*.c a b)               (*.c b a)])

(define-ruleset associativity.c (arithmetic simplify complex)
  #:type ([a complex] [b complex] [c complex])
  [associate-+r+.c     (+.c a (+.c b c))         (+.c (+.c a b) c)]
  [associate-+l+.c     (+.c (+.c a b) c)         (+.c a (+.c b c))]
  [associate-+r-.c     (+.c a (-.c b c))         (-.c (+.c a b) c)]
  [associate-+l-.c     (+.c (-.c a b) c)         (-.c a (-.c b c))]
  [associate--r+.c     (-.c a (+.c b c))         (-.c (-.c a b) c)]
  [associate--l+.c     (-.c (+.c a b) c)         (+.c a (-.c b c))]
  [associate--l-.c     (-.c (-.c a b) c)         (-.c a (+.c b c))]
  [associate--r-.c     (-.c a (-.c b c))         (+.c (-.c a b) c)]
  [associate-*r*.c     (*.c a (*.c b c))         (*.c (*.c a b) c)]
  [associate-*l*.c     (*.c (*.c a b) c)         (*.c a (*.c b c))]
  [associate-*r/.c     (*.c a (/.c b c))         (/.c (*.c a b) c)]
  [associate-*l/.c     (*.c (/.c a b) c)         (/.c (*.c a c) b)]
  [associate-/r*.c     (/.c a (*.c b c))         (/.c (/.c a b) c)]
  [associate-/l*.c     (/.c (*.c b c) a)         (/.c b (/.c a c))]
  [associate-/r/.c     (/.c a (/.c b c))         (*.c (/.c a b) c)]
  [associate-/l/.c     (/.c (/.c b c) a)         (/.c b (*.c a c))]
  [sub-neg.c           (-.c a b)                 (+.c a (neg.c b))]
  [unsub-neg.c         (+.c a (neg.c b))           (-.c a b)])

(define-ruleset distributivity.c (arithmetic simplify complex)
  #:type ([a complex] [b complex] [c complex])
  [distribute-lft-in.c      (*.c a (+.c b c))           (+.c (*.c a b) (*.c a c))]
  [distribute-rgt-in.c      (*.c a (+.c b c))           (+.c (*.c b a) (*.c c a))]
  [distribute-lft-out.c     (+.c (*.c a b) (*.c a c))   (*.c a (+.c b c))]
  [distribute-lft-out--.c   (-.c (*.c a b) (*.c a c))   (*.c a (-.c b c))]
  [distribute-rgt-out.c     (+.c (*.c b a) (*.c c a))   (*.c a (+.c b c))]
  [distribute-rgt-out--.c   (-.c (*.c b a) (*.c c a))   (*.c a (-.c b c))]
  [distribute-lft1-in.c     (+.c (*.c b a) a)           (*.c (+.c b (complex 1 0)) a)]
  [distribute-rgt1-in.c     (+.c a (*.c c a))           (*.c (+.c c (complex 1 0)) a)])

(define-ruleset fractions-distribute.c (fractions simplify complex)
  #:type ([a complex] [b complex] [c complex] [d complex])
  [div-sub.c     (/.c (-.c a b) c)          (-.c (/.c a c) (/.c b c))]
  [times-frac.c  (/.c (*.c a b) (*.c c d))  (*.c (/.c a c) (/.c b d))])

(define-ruleset fractions-transform.c (fractions complex)
  #:type ([a complex] [b complex] [c complex] [d complex])
  [sub-div.c     (-.c (/.c a c) (/.c b c))  (/.c (-.c a b) c)]
  [frac-add.c    (+.c (/.c a b) (/.c c d))  (/.c (+.c (*.c a d) (*.c b c)) (*.c b d))]
  [frac-sub.c    (-.c (/.c a b) (/.c c d))  (/.c (-.c (*.c a d) (*.c b c)) (*.c b d))]
  [frac-times.c  (*.c (/.c a b) (/.c c d))  (/.c (*.c a c) (*.c b d))]
  [frac-2neg.c   (/.c a b)                  (/.c (neg.c a) (neg.c b))])

(define-ruleset* complex-number-basics (complex simplify)
  #:type ([x real] [y real] [a real] [b real] [c real] [d real])
  [real-part        (re (complex x y))     x]
  [imag-part        (im (complex x y))     y]
  [complex-add-def  (+.c (complex a b) (complex c d)) (complex (+ a c) (+ b d))]
  [complex-def-add  (complex (+ a c) (+ b d)) (+.c (complex a b) (complex c d))]
  [complex-sub-def  (-.c (complex a b) (complex c d)) (complex (- a c) (- b d))]
  [complex-def-sub  (complex (- a c) (- b d)) (-.c (complex a b) (complex c d))]
  [complex-neg-def  (neg.c (complex a b)) (complex (neg a) (neg b))]
  [complex-def-neg  (complex (neg a) (neg b)) (neg.c (complex a b))]
  [complex-mul-def  (*.c (complex a b) (complex c d))
                    (complex (- (* a c) (* b d)) (+ (* a d) (* b c)))]
  [complex-div-def  (/.c (complex a b) (complex c d))
                    (complex (/ (+ (* a c) (* b d)) (+ (* c c) (* d d)))
                             (/ (- (* b c) (* a d)) (+ (* c c) (* d d))))]
  [complex-conj-def (conj (complex a b)) (complex a (neg b))])
