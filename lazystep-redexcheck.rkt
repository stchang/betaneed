#lang racket
(require redex)
(require "lazystep.rkt")

(define-metafunction lazystep
  fv : e -> (x ...)
  [(fv e) (remove-duplicates (fv_ e))])
(define-metafunction lazystep
  fv_ : e -> (x ...)
  [(fv_ x)    (x)]
  [(fv_ (e_1 e_2)) (∪ (fv_ e_1) (fv_ e_2))]
  [(fv_ (λ x e))   (set-diff (fv_ e) (x))]
  [(fv_ (lab x e)) (fv e)])
(define-metafunction lazystep
  remove-duplicates : (x ...) -> (x ...)
  [(remove-duplicates ()) ()]
  [(remove-duplicates (x)) (x)]
  [(remove-duplicates (x_1 x_2 ...)) ; x \notin (x_2 ...)
   (x_1 ,@(term (remove-duplicates (x_2 ...))))
   (side-condition (not (memq (term x_1) (term (x_2 ...)))))]
  [(remove-duplicates (x_1 x_2 ...)) ; x \in (x_2 ...)
   (remove-duplicates (x_2 ...))
   (side-condition (memq (term x_1) (term (x_2 ...))))])
(define-metafunction lazystep
  ∪ : (x ...) ... -> (x ...)
  [(∪ (x_1 ...) (x_2 ...) (x_3 ...) ...)
   (∪ (x_1 ... x_2 ...) (x_3 ...) ...)]
  [(∪ (x ...)) (x ...)]
  [(∪)         ()])
(define-metafunction lazystep
  set-diff : (x ...) (x ...) -> (x ...)
  [(set-diff (x ...) ()) (x ...)]
  [(set-diff (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (set-diff (x_1 ... x_3 ...) (x_4 ...))
   (side-condition (not (memq (term x_2) (term (x_1 ... x_3 ...)))))]
  [(set-diff (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (set-diff (x_1 ... x_3 ...) (x_2 x_4 ...))
   (side-condition (memq (term x_2) (term (x_1 ... x_3 ...))))]
  [(set-diff (x_1 ...) (x_2 x_3 ...))
   (set-diff (x_1 ...) (x_3 ...))
   (side-condition (not (memq (term x_2) (term (x_1 ...)))))])
(define (close e)
  (define (make-x i)
    (string->symbol (string-append "x_" (number->string i))))
  (let ([fvs (term (fv ,e))])
    (let L ([e (term (rename-bound-vars ,e ,fvs))] [fvs fvs] [i 1])
      (if (empty? fvs)
          e
          (let ([x (make-x i)])
            (L (term ((λ ,(first fvs) ,e) (λ ,x ,x))) 
               (rest fvs) (add1 i)))))))
;; rename-bound-vars:
;;   rename all bound variables in a given λ abstraction
;;   the second argument is the list of existing bound variables
;;
(define-metafunction lazystep
  rename-bound-vars : e (x ...) -> e
  [(rename-bound-vars (λ x_1 e) (x ...))
   (λ x_new (rename-bound-vars (subst e x_1 x_new) (x_new x ...)))
   (where x_new ,(variable-not-in (term (x ... x_1))
                                  (term x_1)))
   #;(side-condition (when DEBUG
                     (printf "renaming ~a to ~a\n" (term x_1) (term x_new))))]
  [(rename-bound-vars (e_1 e_2) (x ...))
   ((rename-bound-vars e_1 (x ...)) (rename-bound-vars e_2 (x ...)))]
  [(rename-bound-vars x_1 (x ...))
   x_1])
(define-metafunction lazystep
  [(alpha-equiv? e_1 e_2) (alphaeq e_1 e_2 () ())])
(define-metafunction lazystep
  [(alphaeq (λ x_1 e_1) (λ x_2 e_2) (x_3 ...) (x_4 ...))
   (alphaeq e_1 e_2 (x_1 x_3 ...) (x_2 x_4 ...))]
  [(alphaeq (e_1 e_2) (e_3 e_4) (x_1 ...) (x_2 ...))
   ,(and (term (alphaeq e_1 e_3 (x_1 ...) (x_2 ...)))
         (term (alphaeq e_2 e_4 (x_1 ...) (x_2 ...))))]
  [(alphaeq x_1 x_2 (x_3 ...) (x_4 ...))
   ,(= (length (member (term x_1) (term (x_3 ...))))
       (length (member (term x_2) (term (x_4 ...)))))]
  [(alphaeq any_1 any_2 any_3 any_4) #f])
(define-metafunction lazystep
  [(extract-bindings e) (get-bindings e ())])
(define-metafunction lazystep
  [(get-bindings ((λ x e_1) e_2) ((x_1 e) ...))
   (get-bindings e_1 ((x e_2) (x_1 e) ...))]
  [(get-bindings (λ x e) ((x_1 e_1) ...))
   ((x_1 e_1) ...)])
#;(define (AF-equiv? t)
  (printf "checking: ~a\n" t)
  (let ([res1 (apply-red-no-dups* red t)]
        [res2 (apply-red-no-dups* λ-need-red-beta t)])
    (and (= (length res1) 1)
         (= (length res2) 1)
         (redex-match λneed a (first res1))
         (redex-match λ-need A (first res2))
         (let ([res3 (apply-red-no-dups* 
                      λ-need-red-nobeta (first res1))])
             (and (= (length res3) 1)
                  (redex-match λ-need A (first res3))
                  (term (alpha-equiv? ,(first res2) ,(first res3)))
                  #;(equal? (term (extract-bindings ,(first res2)))
                          (term (extract-bindings ,(first res3))))))
           )))
#;(define (AF-equiv-noambig? t)
  (printf "~a) checking: ~a\n" n t)
  (set! n (add1 n))
  (let ([res1 (apply-red-no-ambig* red t)]
        [res2 (apply-red-no-ambig* λ-need-red-beta t)])
    (and (redex-match λneed a res1)
         (redex-match λ-need A res2)
         (let ([res3 (apply-red-no-ambig* λ-need-red-nobeta res1)])
           (redex-match λ-need A res3)
           (term (alpha-equiv? ,res2 ,res3))))))
(define (lazystep-v? t)
  (printf "~a) checking: ~a\n" n t)
  (set! n (add1 n))
  (let loop ([t t])
    (let ([res1 (apply-reduction-relation lazystep-red t)])
      (cond [(null? res1) (redex-match lazystep v t)]
            [(= (length res1) 1) (loop (car res1))]
            [else #f]))))
#;(define (CF-CK-bisim? t)
  (printf "~a) checking: ~a\n" n t)
  (set! n (add1 n))
  (let loop ([t (term (,t (mt)))])
    (let ([res1 (apply-reduction-relation red-ck t)])
      (cond
        [(null? res1)
         (redex-match λneed a (term (φ ,t)))]
        [(= (length res1) 1)
         (if (term (alpha-equiv? (φ ,(car res1)) (φ ,t)))
             (loop (car res1))
             (let ([res2 (apply-reduction-relation red (term (φ ,t)))])
               (term (alpha-equiv? (φ ,(car res1)) ,(car res2)))))]
        [else #f]))))
#;(define (gen-trace-ck t)
  (define (gen-trace-ck-help t)
    (let ([res (apply-reduction-relation red-ck t)])
          (if (null? res)
              (list t)
              (cons t (gen-trace-ck-help (car res))))))
  (gen-trace-ck-help (term (,t (mt)))))
(define n 1)
(define-syntax (redex-check-go stx)
  (syntax-case stx ()
    [(_) #'(redex-check lazystep d (lazystep-v? (term d)) 
                        #:prepare close 
                        #:attempts 1000000)]))
(define-syntax (traces-ck stx)
  (syntax-case stx ()
  [(_ red t) #'(traces red (term (,t (mt))))]))
;(redex-check-go)