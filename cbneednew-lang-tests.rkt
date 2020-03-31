#lang racket
(require redex)
(require test-engine/racket-tests)
(require (only-in "cbneednew.rkt" λneed valid-E?))

(define-syntax (A? stx)
  (syntax-case stx ()
    [(_ t) #'(redex-match λneed A (term t))]))
(define-syntax (E? stx)
  (syntax-case stx ()
    [(_ t) #'(redex-match λneed 
                          (side-condition E_1 (term (valid-E? E_1))) 
                          (term t))]))
(define-syntax (check stx)
  (syntax-case stx ()
    [(_ a? t) (syntax/loc #'t (check-expect (not (a? t)) #f))]))
(define-syntax (check-not stx)
  (syntax-case stx ()
    [(_ a? t) (syntax/loc #'t (check-expect (a? t) #f))]))

(check A? hole)
(check-not A? (hole))
(check-not A? (hole x))
(check-not A? (λ x x))
(check-not A? (λ x hole))
(check-not A? ((λ x hole)))
(check A? ((λ x hole) x))
(check A? ((λ x hole) y))
(check-not A? ((λ x hole) x y))
(check-not A? (((λ x hole) x) y))
(check A? (((λ y (λ x hole)) x) y))
(check A? (((λ y (λ x hole)) y) x))
(check-not A? ((λ y (λ x hole)) x y z))
(check-not A? ((((λ y (λ x hole)) x) y) z))
(check A? ((((λ z (λ y (λ x hole))) x) y) z))
(check A? ((λ y ((λ x hole) b)) c))
(check A? ((λ z ((λ y ((λ x hole) b)) c)) d))
(check A? ((λ z ((λ y ((λ x ((((λ x (λ y (λ z hole))) b) c) d)) b)) c)) d))
(check-not A? ((λ z ((λ y ((λ x (((λ x (λ y (λ z hole))) b) c)) b)) c)) d))
(check-not A? (λ z ((λ y ((λ x ((((λ x (λ y (λ z hole))) b) c) d)) b)) c)))
(check-not A? ((λ z ((λ y ((λ x (((((λ x (λ y (λ z hole))) b) c) d) f)) b)) c)) d))


(check E? hole)
(check E? (((hole x) y) z))
(check-not E? (((x hole) y) z))
(check E? ((λ x hole) y))
(check-not E? (λ x hole))
(check-not E? ((λ x hole)))
(check E? ((((λ x hole) x) y) z))
(check E? (((((λ y (λ x hole)) z) b) c) d))
(check E?   (((((λ z ((λ y (λ x hole)) z)) w) b) c) d))
(check E?  ((((((λ z (λ y (λ x hole))) b) c) d) f) g))
(check E?    ((((λ z (λ y (λ x hole))) b) c) d))
(check-not E? ((((λ z (λ y (λ x hole))) b) c)))

; i = n+1
(check E? ((λ x x) hole))
(check E? ((λ x (x y)) hole))
(check E? (((λ y (λ x x)) b) hole))
(check E? (((λ z ((λ y (λ x x)) b)) c) hole))
(check E? ((((λ z (λ y (λ x x))) b) c) hole))

; i \in 1...n
(check-not E? ((λ x x) y hole))
(check-not E? (((λ x x) y) hole))
(check-not E? ((λ x (λ y (x y))) hole))
(check-not E? ((λ x (λ y (x y))) hole z))
(check E? (((λ x (λ y (x y))) hole) z))
(check E? (((λ x (λ y (y x))) z) hole))
(check E? ((((λ x (λ y (λ z ((x y) z)))) hole) b) c))
(check E? ((((λ x (λ y (λ z ((y x) z)))) b) hole) c))
(check E? ((λ x ((λ y ((λ z ((y x) z)) c)) hole)) b)) ; non-hole inner E
(check E? ((((λ x (λ y (λ z ((z x) y)))) c) d) hole))
(check E? (((((λ x (λ y (λ z ((z x) y)))) c) d) hole) f))
(check E? (((((λ w (λ x (λ y (λ z ((x y) (z w)))))) w) hole) y) z))
(check-not E? (((((λ w (λ x (λ y (λ z ((x y) (z w)))))) hole) x) y) z))
(check-not E? (((((λ w (λ x (λ y (λ z ((x y) (z w)))))) w) x) hole) z))
(check-not E? (((((λ w (λ x (λ y (λ z ((x y) (z w)))))) w) x) y) hole))
(check 
 E? 
 (((((λ w (λ x (λ y (((λ x_2 (λ x_1 (λ z ((x y) (w z))))) x_1) x_2)))) 
     w) hole) y) z)) ; non-hole inner A
(check 
 E? 
 (((((λ w (λ x (λ y (((λ x_2 (λ x_1 (λ z ((z y) (w x))))) x_1) x_2)))) 
     w) x) y) hole)) ; non-hole inner A
(check E? (((λ x ((λ y (λ z hole)) b)) c) d)) ; Casey's example
           



(test)