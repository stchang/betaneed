#lang racket
(require redex)
;(require test-engine/racket-tests)
(require (only-in "cbneednew.rkt" red apply-red-no-dups* apply-red-no-ambig*))

(define-syntax (check-red stx)
  (syntax-case stx (-->)
    [(_ t --> expected)
     #`(let ([res (apply-red-no-ambig* red (term t))])
         #,(syntax/loc stx (test-->> red res (term expected))))]
    #;[(_ t --> expected)
     #`(let ([res (apply-red-no-dups* red (term t))])
         (unless (= (length res) 1) (printf "(length res) = ~a\n" (length res)))
         #,(syntax/loc stx (test-->> red (car res) (term expected))))]
    #;[(_ t --> expected)
     (syntax/loc stx (test-->> red (term t) (term expected)))]))

(check-red (λ x x) --> (λ x x))
(check-red ((λ x x) (λ x_1 x_1)) --> (λ x_2 x_2))
(check-red (((λ y (λ x (y x))) (λ x_1 x_1)) (λ x_2 x_2)) 
           --> 
           (λ x_3 x_3))
(check-red (((λ y (λ x (x y))) (λ x_1 x_1)) (λ x_2 x_2))
           -->
           (λ x_2 x_2))
(check-red ((((λ x (λ y (λ z ((x y) z)))) (λ x_1 x_1)) (λ x_2 x_2)) (λ x_3 x_3))
           -->
           (λ x_2 x_2))
(check-red ((((λ x (λ y (λ z ((y x) z)))) (λ x_1 x_1)) (λ x_2 x_2)) (λ x_3 x_3))
           -->
           (λ x_2 x_2))
(check-red ((((λ x (λ y (λ z ((z x) y)))) (λ x_1 x_1)) (λ x_2 x_2)) (λ x_3 x_3))
           -->
           (λ x_2 x_2))
(check-red (((λ z ((λ y (λ x x)) (λ x_1 x_1))) (λ x_2 x_2)) (λ x_3 x_3))
           -->
           ((λ z1 ((λ y1 (λ x_4 x_4)) (λ x_4 x_4))) (λ x_4 x_4)))
(check-red (((λ z ((λ y (λ x y)) (λ x_1 x_1))) (λ x_2 x_2)) (λ x_3 x_3))
           -->
           (((λ z (λ x4 (λ x_4 x_4))) (λ x_2 x_2)) (λ x_3 x_3)))
(check-red (((λ z ((λ y (λ x z)) (λ x_1 x_1))) (λ x_2 x_2)) (λ x_3 x_3))
           -->
           (((λ y1 (λ x4 (λ x_4 x_4))) (λ x_1 x_1)) (λ x_3 x_3)))
; Casey's example
(check-red (((λ x ((λ y (λ z x)) (λ x_1 x_1))) (λ x_2 x_2)) (λ x_3 x_3))
           -->
           (((λ y1 (λ z1 (λ x_4 x_4))) (λ x_1 x_1)) (λ x_3 x_3)))
(check-red (((λ x ((λ y (λ z y)) (λ x_1 x_1))) (λ x_2 x_2)) (λ x_3 x_3))
           -->
           (((λ x (λ z1 (λ x_4 x_4))) (λ x_2 x_2)) (λ x_3 x_3)))
(check-red (((λ x ((λ y (λ z z)) (λ x_1 x_1))) (λ x_2 x_2)) (λ x_3 x_3))
           -->
           ((λ x4 ((λ y1 (λ x_4 x_4)) (λ x_4 x_4))) (λ x_4 x_4)))
; Casey's example used as A in arg
(check-red 
 ((λ x_9 x_9) 
  (((λ x ((λ y (λ z (λ x_8 x_8))) (λ x_1 x_1))) (λ x_2 x_2)) (λ x_3 x_3)))
 -->
 (((λ x4 ((λ y1 (λ z1 (λ x_4 x_4))) (λ x_4 x_4))) (λ x_4 x_4)) (λ x_4 x_4)))
; Casey's example used as intermediate A
(check-red
 ((((λ x_8 (λ x_9 (((λ x ((λ y (λ z (λ x_4 (x_8 x_9)))) (λ x_1 x_1))) (λ x_2 x_2)) (λ x_3 x_3)))) (λ x_5 x_5)) (λ x_6 x_6)) (λ x_7 x_7))
 -->
((((λ x3 ((λ y2 (λ z2 (λ x_3 (λ x_4 x_4)))) (λ x_1 x_1))) (λ x_1 x_1)) (λ x_1 x_1)) (λ x_7 x_7)))
(check-red
 ((((λ x (λ y (((λ x ((λ y (λ z (λ x_4 (x y)))) (λ x_1 x_1))) (λ x_2 x_2)) (λ x_3 x_3)))) (λ x_5 x_5)) (λ x_6 x_6)) (λ x_7 x_7))
 -->
 ((((λ x (λ y ((λ z2 (λ x_4 (λ x_8 x_8))) (λ x_3 x_3)))) (λ x_5 x_5)) (λ x_6 x_6)) (λ x_7 x_7)))
(check-red
 ((((λ x (λ x (((λ x ((λ y (λ z (λ x_4 (x y)))) (λ x_1 x_1))) (λ x_2 x_2)) (λ x_3 x_3)))) (λ x_5 x_5)) (λ x_6 x_6)) (λ x_7 x_7))
 -->
 ((((λ x (λ x ((λ z2 (λ x_4 (λ x_8 x_8))) (λ x_3 x_3)))) (λ x_5 x_5)) (λ x_6 x_6)) (λ x_7 x_7)))
(check-red
 (((λ x (λ x (x x))) (λ x_1 x_1)) (λ x_2 x_2))
 -->
 ((λ x3 (λ x_1 x_1)) (λ x_3 x_3)))
; arg is ans that must be shared (from AF cbneed paper)
(check-red
 ((λ x ((x (λ x_1 x_1)) (x (λ x_2 x_2)))) ((λ z (λ w (z w))) ((λ x_3 x_3) (λ x_4 x_4))))
 -->
 (λ x_1 x_1))

; demonstrate need to rename A on lhs
(check-red
 ((λ x (((λ x (λ y y)) (λ x_1 x_1)) (λ z x))) (λ x_3 x_3))
 -->
 ((λ x ((λ x2 (λ z1 x)) (λ x_2 x_2))) (λ x_3 x_3)))

; redex-check counterexamples
; exposed renaming issue (A around op needs to be renamed)
(check-red
 ((λ BF
   ((λ i
      ((λ /R
         ((λ ZQ
            ((λ Og1
               ((λ J2
                  (((λ D3
                      (λ l1
                        (λ x_1
                          x_1)))
                    (J2 Og1))
                   (((ZQ /R)
                     i)
                    (λ T2
                      BF))))
                (λ x_2 x_2)))
             (λ x_3 x_3)))
          (λ x_99 x_99)))
       (λ x_99 x_99)))
    (λ x_99 x_99)))
 (λ x_99 x_99))
 -->
 ((λ BF
   ((λ i
      ((λ /R
         ((λ ZQ
            ((λ Og1
               ((λ J2
                  (((λ D3
                      (λ l1
                        (λ x_1
                          x_1)))
                    (J2 Og1))
                   (((ZQ /R)
                     i)
                    (λ T2
                      BF))))
                (λ x_2 x_2)))
             (λ x_3 x_3)))
          (λ x_99 x_99)))
       (λ x_99 x_99)))
    (λ x_99 x_99)))
 (λ x_99 x_99)))

; exposed need to remove innermost λ around innermost E
(check-red
 ((λ f
    ((λ T
       ((λ b
          ((λ k
             ((λ ′ (((λ x (λ k x)) ((λ y (′ (λ * k))) (b (λ I T)))) f))
              (λ x_1 x_1)))
           (λ x_2 x_2)))
        (λ x_3 x_3)))
     (λ x_4 x_4)))
  (λ x_5 x_5))
 -->
 ((λ f
    ((λ T
       ((λ b ((λ k (((λ y2 (λ k2 (λ *1 k))) (b (λ I2 T))) f)) (λ x_2 x_2)))
        (λ x_3 x_3)))
     (λ x_4 x_4)))
  (λ x_5 x_5)))
 

; redex-check/apply-reduction-relation seemed to get stuck?
; - fixed with apply-red-no-dups*
(check-red
((λ Id ((λ zT ((λ T ((λ y ((λ P ((λ o ((λ s (((s o) (P y)) ((λ R T) (zT Id)))) (λ x_1 x_1))) (λ x_2 x_2))) (λ x_3 x_3))) (λ x_4 x_4))) (λ x_5 x_5))) (λ x_6 x_6))) (λ x_7 x_7))
 -->
 ((λ Id ((λ zT ((λ R2 (λ x_3 x_3)) (zT Id))) (λ x_6 x_6))) (λ x_7 x_7)))

(check-red
 ((λ K ((λ d ((λ Q ((λ HA ((λ c ((λ u ((λ pf (pf (((λ smu u) c) ((HA Q) (d K))))) (λ x_1 x_1))) (λ x_2 x_2))) (λ x_3 x_3))) (λ x_4 x_4))) (λ x_5 x_5))) (λ x_6 x_6))) (λ x_7 x_7))
 -->
 ((λ c1 ((λ smu2 (λ x_3 x_3)) c1)) (λ x_1 x_1)))


; crashed redex-check
(check-red
 ((λ d
    ((λ four
       ((λ nine
          ((λ Q
             ((λ g
                ((λ P
                   ((λ Dc
                      ((λ NS
                         ((λ mq
                            ((λ q
                               ((λ b
                                  ((λ u
                                     ((λ Zn
                                        ((λ am
                                           ((λ I
                                              (((((λ L (λ K I)) (λ W (λ me am)))
                                                 (λ c Zn))
                                                (λ w (λ Ze u)))
                                               (((((b q) mq) ((NS Dc) (P g)))
                                                 ((λ q (λ N Q)) (λ yu
                                                                  (λ h nine))))
                                                (four d))))
                                            (λ x_1 x_1)))
                                         (λ x_2 x_2)))
                                      (λ x_3 x_3)))
                                   (λ x_4 x_4)))
                                (λ x_5 x_5)))
                             (λ x_6 x_6)))
                          (λ x_7 x_7)))
                       (λ x_8 x_8)))
                    (λ x_9 x_9)))
                 (λ x_10 x_10)))
              (λ x_11 x_11)))
           (λ x_12 x_12)))
        (λ x_13 x_13)))
     (λ x_14 x_14)))
  (λ x_15 x_15))
 -->
 ((λ d
     ((λ four
        ((λ nine
           ((λ Q
              ((λ g
                 ((λ P
                    ((λ Dc
                       ((λ NS
                          ((λ mq
                             ((λ q
                                ((λ b
                                   ((λ u
                                      ((λ Zn
                                         ((λ am
                                            ((((λ L2 (λ K2 (λ w2 (λ Ze2 u))))
                                               (λ W2 (λ me2 am)))
                                              (λ c2 Zn))
                                             (((((b q) mq) ((NS Dc) (P g)))
                                               ((λ q1 (λ N1 Q)) (λ yu1 (λ h1 nine))))
                                              (four d))))
                                          (λ x_2 x_2)))
                                       (λ x_3 x_3)))
                                    (λ x_4 x_4)))
                                 (λ x_5 x_5)))
                              (λ x_6 x_6)))
                           (λ x_7 x_7)))
                        (λ x_8 x_8)))
                     (λ x_9 x_9)))
                  (λ x_10 x_10)))
               (λ x_11 x_11)))
            (λ x_12 x_12)))
         (λ x_13 x_13)))
      (λ x_14 x_14)))
   (λ x_15 x_15)))

; this example needs the x_1 \notin (bound-vars E_1) side-condition
(check-red
 ((λ U
   ((λ W
      ((λ x
         ((λ q ((λ F ((((λ F F) ((F q) (λ y x))) (λ c (λ J W))) U)) (λ x_1 x_1)))
          (λ x_2 x_2)))
       (λ x_3 x_3)))
    (λ x_4 x_4)))
 (λ x_5 x_5))
 -->
 ((λ W1 ((λ y1 (λ x_3 x_3)) (λ c1 (λ J1 W1)))) (λ x_1 x_1)))


(test-results)
;(test)