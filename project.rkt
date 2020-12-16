;; PL Project - Spring 2020
;; NUMEX interpreter
;; author - moh.robati

#lang racket
(provide (all-defined-out))

;; definition of structures for NUMEX programs
(struct var (string) #:transparent) ;; done
(struct num (int) #:transparent) ;; done
(struct bool (b) #:transparent) ;; done
(struct plus (e1 e2) #:transparent) ;; done
(struct minus (e1 e2) #:transparent) ;; done
(struct mult (e1 e2) #:transparent) ;; done
(struct div (e1 e2) #:transparent) ;; done
(struct neg (e1) #:transparent) ;; done
(struct andalso (e1 e2) #:transparent) ;; done
(struct orelse (e1 e2) #:transparent) ;; done
(struct cnd (e1 e2 e3) #:transparent) ;; done
(struct iseq (e1 e2) #:transparent) ;; done
(struct ifnzero (e1 e2 e3) #:transparent) ;; done
(struct ifleq (e1 e2 e3 e4) #:transparent) ;; done
(struct munit () #:transparent) ;; done
(struct ismunit (e) #:transparent) ;; done
(struct apair (e1 e2) #:transparent) ;; done
(struct 1st (e1) #:transparent) ;; done
(struct 2nd (e1) #:transparent) ;; done
(struct queue (e q) #:transparent) ;; done
(struct enqueue (e q) #:transparent) ;; done
(struct dequeue (q) #:transparent) ;; done
(struct extract (q) #:transparent) ;; done
(struct lam  (nameopt formal body) #:transparent) ;; done
(struct apply (funexp actual) #:transparent) ;; done
(struct with  (s e1 e2) #:transparent) ;; done
(struct closure (env f) #:transparent) ;; done
(struct letrec (s1 e1 s2 e2 s3 e3 e4) #:transparent) ;; done

;; Problem 1

(define (racketlist->numexlist xs)
  (cond [(null? xs) (munit)]
        [true (apair (car xs) (racketlist->numexlist (cdr xs)))]))

(define (numexlist->racketlist xs)
  (cond [(munit? xs) empty]
        [true (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))]))

;; Problem 2

;; environment is like a dictionary
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
  	[(eq? (car(car env)) str) (cdr(car env))]
        [#t (envlookup (cdr env) str)]))

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.

(define (eval-under-env e env)
  (cond [(var? e)
         (let ([v1 (eval-under-env (var-string e) env)])
         (if (string? (var-string e))
             (envlookup env (var-string e)) (error "NUMEX var applied to non-string")))]
        
        [(num? e)
         (let ([v1 (eval-under-env (num-int e) env)])
         (if (integer? v1) (num v1) (error "NUMEX num applied to non-integer")))]
         
        [(bool? e)
         (let ([v1 (eval-under-env (bool-b e) env)])
         (if (boolean? v1) (bool v1) (error "NUMEX bool appllied to non-boolean")))]

        [(plus? e) 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX plus applied to non-num")))]
        
        [(minus? e) 
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1) 
                       (num-int v2)))
               (error "NUMEX minus applied to non-num")))]
        
        [(mult? e) 
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1) 
                       (num-int v2)))
               (error "NUMEX mult applied to non-num")))]
        
        [(div? e) 
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (if (eq? (num-int v2) 0)
                   (error "NUMEX division applied to zero" v2)
                   (num (quotient (num-int v1) 
                       (num-int v2))))
               (error "NUMEX division applied to non-num")))]
        
        [(neg? e) 
         (let ([v1 (eval-under-env (neg-e1 e) env)])
           (if (num? v1)
               (num (- (num-int v1)))
               (if (bool? v1)
                   (bool (if (bool-b v1) #f #t))
                   (error "NUMEX neg applied to non-num or non-bool"))))]
        
        [(andalso? e) 
         (let ([v1 (eval-under-env (andalso-e1 e) env)])
           (let ([v2 (cond[(bool? v1) v1]
                          [(num? v1) (if (eq? (num-int v1) 0) (bool #f) (bool #t))]
                          [#t error "NUMEX andalso applied to non-num or non-bool"])])
             (if (and (bool? v2) (eq? (bool-b v2) #f))
                 (bool #f)
                 (let ([v3 (eval-under-env (andalso-e2 e) env)])
                   (let ([v4 (cond[(bool? v3) v3]
                                  [(num? v3) (if (eq? (num-int v3) 0) (bool #f) (bool #t))]
                                  [#t error "NUMEX andalso applied to non-num or non-bool"])])
                     v4)))))]
        
        [(orelse? e)
         (let ([v1 (eval-under-env (orelse-e1 e) env)])
           (let ([v2 (cond[(bool? v1) v1]
                          [(num? v1) (if (eq? (num-int v1) 0) (bool #f) (bool #t))]
                          [#t error "NUMEX orelse applied to non-num or non-bool"])])
             (if (and (bool? v2) (eq? (bool-b v2) #t))
                 (bool #t)
                 (let ([v3 (eval-under-env (orelse-e2 e) env)])
                   (let ([v4 (cond[(bool? v3) v3]
                                  [(num? v3) (if (eq? (num-int v3) 0) (bool #f) (bool #t))]
                                  [#t error "NUMEX orelse applied to non-num or non-bool"])])
                     v4)))))]
        
       [(cnd? e)
        (let ([v1 (eval-under-env (cnd-e1 e) env)])
              (if (bool? v1)
                  (if (bool-b v1)
                      (eval-under-env (cnd-e2 e) env)
                      (eval-under-env (cnd-e3 e) env))
                  (error "NUMEX cnd condition applied to non-bool")))]

       [(iseq? e)
        (let ([v1 (eval-under-env (iseq-e1 e) env)]
              [v2 (eval-under-env (iseq-e2 e) env)])
              (cond
                [(and (num? v1)(num? v2))
                 (bool (eq? (num-int v1) (num-int v2)))]
                [(and (bool? v1)(bool? v2))
                 (bool (eq? (bool-b v1)(bool-b v2)))]
                [#t (bool #f)]))]

       [(ifnzero? e)
        (let ([v1 (eval-under-env (ifnzero-e1 e) env)])
              (if (num? v1)
                  (if (eq? (num-int v1) 0)
                      (eval-under-env (ifnzero-e3 e) env)
                      (eval-under-env (ifnzero-e2 e) env))
                  (error "NUMEX ifnzero applied to a non-num")))]

       [(ifleq? e)
        (let ([v1 (eval-under-env (ifleq-e1 e) env)]
              [v2 (eval-under-env (ifleq-e2 e) env)])
              (if (and (num? v2)
                       (num? v1))
                  (if (<= (num-int v1)(num-int v2))
                      (eval-under-env (ifleq-e3 e) env)
                      (eval-under-env (ifleq-e4 e) env))
                  (error "NUMEX ifleq applied to a non-num")))]

       [(munit? e)
        (munit)]
       
       [(ismunit? e)
        (let ([v1 (eval-under-env (ismunit-e e) env)])
              (bool (munit? v1))
         )]

       [(apair? e)
        (let ([v1 (eval-under-env (apair-e1 e) env)]
              [v2 (eval-under-env (apair-e2 e) env)])
              (apair v1 v2))]

       [(1st? e)
        (let ([v1 (eval-under-env (1st-e1 e) env)])
          (if (apair? v1)
              (apair-e1 v1)
              (error "NUMEX 1st applied to non-apair")))]

       [(2nd? e)
        (let ([v1 (eval-under-env (2nd-e1 e) env)])
          (if (apair? v1)
              (apair-e2 v1)
              (error "NUMEX 2nd applied to non-apair")))]

       [(queue? e)
         (let([v1 (eval-under-env (queue-e e) env)]
              [v2 (eval-under-env (queue-q e) env)])
           (if (or (queue? v2)(munit? v2))
               (queue v1 v2)
               (error "NUMEX queue applied to non-queue")))]
       
       [(enqueue? e)
         (let([v1 (eval-under-env (enqueue-e e) env)]
              [v2 (eval-under-env (enqueue-q e) env)])
           (if (or (queue? v2)(munit? v2))
               (queue v1 v2)
               (error "NUMEX enqueue applied to non-queue")))]
       
       [(dequeue? e)
         (let([v1 (eval-under-env (dequeue-q e) env)])
           (if (queue? v1)
              (if (munit? (queue-q v1))
                   (munit)
                   (queue (queue-e v1) (eval-under-env (dequeue (queue-q v1)) env)))
               (error "NUMEX dequeue applied to non-queue")))]
       
       [(extract? e)
         (let([v1 (eval-under-env (extract-q e) env)])
           (if (queue? v1)
               (if (munit? (queue-q v1))
                   (queue-e v1)
                   (eval-under-env (extract (queue-q v1)) env))
               (error "NUMEX extract applied to non-queue")))]

       [(lam? e)
         (if (and (or (string? (lam-nameopt e)) (null? (lam-nameopt e)))
                  (string? (lam-formal e)))
             (closure env e)
             (error "NUMEX lambda name or arg applied to non-string"))] 

       [(apply? e)
          (let ([evaledFunexp (eval-under-env (apply-funexp e) env)])
            (if (or (closure? evaledFunexp) (lam? evaledFunexp))
              (if (lam? evaledFunexp)
                (let* ([funlam (eval-under-env evaledFunexp env)] 
                      [exec (closure-f funlam)])
                  (if (lam? exec)
                    (let ([evaledParameter (eval-under-env (apply-actual e) env)])
                      (eval-under-env (lam-body exec) (cons (cons (lam-formal exec) evaledParameter)
                                                      (cons (cons (lam-nameopt exec) funlam) (closure-env funlam)))))
                    (error "apply applied to non-executable function")))
                (let ([exec (closure-f evaledFunexp)])
                  (if (lam? exec)
                    (let ([evaledParameter (eval-under-env (apply-actual e) env)])
                      (eval-under-env (lam-body exec) (cons (cons (lam-formal exec) evaledParameter)
                                                      (cons (cons (lam-nameopt exec) evaledFunexp) (closure-env evaledFunexp)))))
                    (error "apply applied to non-executable function"))))
              (error  "apply applied to non-function and non-closure" )))]

       [(letrec? e) 
          (eval-under-env (letrec-e4 e)
                          (cons (cons (letrec-s1 e)
                                      (letrec-e1 e))
                                (cons (cons (letrec-s2 e)
                                            (letrec-e2 e))
                                      (cons (cons (letrec-s3 e)
                                                  (letrec-e3 e)) env))))]

       [(with? e)
        (eval-under-env (with-e2 e)
                        (cons (cons (with-s e)(eval-under-env (with-e1 e) env)) env))]

       [(string? e) e]
       [(number? e)  e]
       [(boolean? e) e]
       [(closure? e) e]
       [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change

(define (eval-exp e)
  (eval-under-env e null))
        
;; Problem 3

(define (ifmunit e1 e2 e3)
  (cnd (ismunit e1) e2 e3))

(define (with* bs e2)
  (if (empty? bs) e2
      (with (car (car bs)) (cdr (car bs)) (with* (cdr bs) e2))))

(define (ifneq e1 e2 e3 e4)
  (with* (cons (cons "_x" e1) (cons (cons "_y" e2) null))
           (cnd (iseq (var "_x") (var "_y")) e4 e3)))

;; Problem 4

(define numex-filter
  (lam null "func"
       (lam "mapFunc" "l"
            (ifmunit (var "l")
                     (munit)
                     (ifnzero (apply (var "func") (1st (var "l")))
                              (apair (apply (var "func") (1st (var "l")))
                                     (apply (var "mapFunc") (2nd (var "l"))))
                              (apply (var "mapFunc") (2nd (var "l"))))))))

(define numex-all-gt
  (with "filter" numex-filter
        (lam null "limit"
             (lam null "l"
                  (apply
                   (apply
                    (var "filter")
                    (lam "gt" "num"
                         (ifleq (var "num") (var "limit")
                                (num 0) 
                                (var "num"))))
                   (var "l"))))))