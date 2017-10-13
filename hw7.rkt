#lang plai-typed
(require plai-typed/s-exp-match)

(define-type Value
  [numV (n : number)]
  [closV (args : (listof symbol))
         (body : ExprC)
         (env : Env)]
  [contV (k : Cont)])

(define-type ExprC
  [numC (n : number)]
  [idC (s : symbol)]
  [plusC (l : ExprC) 
         (r : ExprC)]
  [multC (l : ExprC)
         (r : ExprC)]
  [lamC (ns : (listof symbol))
        (body : ExprC)]
  [appC (fun : ExprC)
        (args : (listof ExprC))]
  [let/ccC (n : symbol)
           (body : ExprC)]
  [negC (arg : ExprC)]
  [avgC (l : ExprC)
        (m : ExprC)
        (r : ExprC)]
  [if0C (tst : ExprC)
        (thn : ExprC)
        (els : ExprC)]
  [tryC (body : ExprC)
        (handler : ExprC)])

(define-type Binding
  [bind (name : symbol)
        (val : Value)])

(define-type-alias Env (listof Binding))

(define mt-env empty)
(define extend-env cons)
(define extend-env* append)

(define-type Cont
  [doneK]
  [addSecondK (r : ExprC)
              (e : Env)
              (k : Cont)]
  [doAddK (v : Value)
          (k : Cont)]
  [multSecondK (r : ExprC)
               (e : Env)
               (k : Cont)]
  [doMultK (v : Value)
           (k : Cont)]
  [appArgK (args : (listof ExprC))
           (env : Env)
           (k : Cont)]
  [appNextArgK (args : (listof ExprC))
               (vals : (listof Value))
               (env : Env)
               (func : Value)
               (k : Cont)]
  [doAppK (vals : (listof Value))
          (k : Cont)]
  [doSecondAvgK (m : ExprC)
                (r : ExprC)
                (env : Env)
                (k : Cont)]
  [doThirdAvgK (l : Value)
               (r : ExprC)
               (env : Env)
               (k : Cont)]
  [doAverageK (sum1 : Value)
              (k : Cont)]
  [doNegateK (k : Cont)]
  [doIf0K (thn : ExprC)
          (els : ExprC)
          (env : Env)
          (k : Cont)])

(module+ test
  (print-only-errors true))

;; parse ----------------------------------------
(define (parse [s : s-expression]) : ExprC
  (cond
    [(s-exp-match? `NUMBER s) (numC (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idC (s-exp->symbol s))]
    [(s-exp-match? '{+ ANY ANY} s)
     (plusC (parse (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
    [(s-exp-match? '{* ANY ANY} s)
     (multC (parse (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
    [(s-exp-match? '{let {[SYMBOL ANY]} ANY} s)
     (let ([bs (s-exp->list (first
                             (s-exp->list (second
                                           (s-exp->list s)))))])
       (appC (lamC (list (s-exp->symbol (first bs)))
                   (parse (third (s-exp->list s))))
             (list (parse (second bs)))))]
    [(s-exp-match? '{lambda {SYMBOL ...} ANY} s)
     (lamC (map s-exp->symbol (s-exp->list 
                               (second (s-exp->list s))))
           (parse (third (s-exp->list s))))]
    [(s-exp-match? '{let/cc SYMBOL ANY} s)
     (let/ccC (s-exp->symbol (second (s-exp->list s)))
              (parse (third (s-exp->list s))))]
    [(s-exp-match? '{neg ANY} s)
     (negC (parse (second (s-exp->list s))))]
    [(s-exp-match? '{avg ANY ANY ANY} s)
     (avgC (parse (second (s-exp->list s)))
           (parse (third (s-exp->list s)))
           (parse (fourth (s-exp->list s))))]
    [(s-exp-match? '{if0 ANY ANY ANY} s)
     (if0C (parse (second (s-exp->list s)))
           (parse (third (s-exp->list s)))
           (parse (fourth (s-exp->list s))))]
    [(s-exp-match? '{try ANY {lambda {} ANY}} s)
     (tryC (parse (second (s-exp->list s)))
           (parse (third (s-exp->list (third (s-exp->list s))))))]
    [(s-exp-match? '{ANY ANY ...} s)
     (appC (parse (first (s-exp->list s)))
           (map parse (rest (s-exp->list s))))]
    [else (error 'parse "invalid input")]))

(module+ test
  (test (parse '2)
        (numC 2))
  (test (parse `x) ; note: backquote instead of normal quote
        (idC 'x))
  (test (parse '{+ 2 1})
        (plusC (numC 2) (numC 1)))
  (test (parse '{* 3 4})
        (multC (numC 3) (numC 4)))
  (test (parse '{+ {* 3 4} 8})
        (plusC (multC (numC 3) (numC 4))
               (numC 8)))
  (test (parse '{let {[x {+ 1 2}]}
                  y})
        (appC (lamC (list 'x) (idC 'y))
              (list (plusC (numC 1) (numC 2)))))
  (test (parse '{lambda {x} 9})
        (lamC (list 'x) (numC 9)))
  (test (parse '{let/cc k 0})
        (let/ccC 'k (numC 0)))
  (test (parse '{double 9})
        (appC (idC 'double) (list (numC 9))))
  (test/exn (parse '{})
            "invalid input")
  (test (parse '{neg 1})
        (negC (numC 1)))
  (test (parse '{avg 1 2 3})
        (avgC (numC 1) (numC 2) (numC 3)))
  (test (parse '{if0 1 2 3})
        (if0C (numC 1) (numC 2) (numC 3)))
  (test (parse '{try {+ 1 2} {lambda {} 8}})
        (tryC (plusC (numC 1) (numC 2))
              (numC 8))))

;; interp & continue ----------------------------------------
(define (interp [a : ExprC] [env : Env] [k : Cont] [handler : Cont]) : Value
  (type-case ExprC a
    [numC (n) (continue k (numV n))]
    [idC (s) (continue k (lookup s env))]
    [plusC (l r) (interp l env
                         (addSecondK r env k))]
    [multC (l r) (interp l env
                         (multSecondK r env k))]
    [lamC (ns body)
          (continue k (closV ns body env))]
    [appC (fun args) (interp fun env
                             (appArgK args env k))]
    [let/ccC (n body)
             (interp body
                     (extend-env (bind n (contV k))
                                 env)
                     k)]
    [negC (n) (interp n env
                      (doNegateK k))]
    [avgC (l m r) (interp l env
                          (doSecondAvgK m r env k))]
    [if0C (tst thn els) (interp tst env
                                (doIf0K thn els env k))]
    [tryC (body handler) (numV 1)]))

(define (continue [k : Cont] [v : Value]) : Value
  (type-case Cont k
    [doneK () v]
    [addSecondK (r env next-k)
                (interp r env
                        (doAddK v next-k))]
    [doAddK (v-l next-k)
            (continue next-k (num+ v-l v))]
    [multSecondK (r env next-k)
                (interp r env
                        (doMultK v next-k))]
    [doMultK (v-l next-k)
             (continue next-k (num* v-l v))]
    [appArgK (args env next-k)
             (if (empty? args)
                 (continue (doAppK empty next-k) v)
                 (interp (first args) env
                         (appNextArgK (rest args) empty env v next-k)))]
    [appNextArgK (args vals env func next-k)
                 (if (empty? args)
                     (continue (doAppK (bak-cons v vals) next-k) func)
                     (interp (first args) env
                             (appNextArgK (rest args) (bak-cons v vals) env func next-k)))]
    [doAppK (vals next-k)
            (type-case Value v
              [closV (ns body c-env)
                     (interp body
                             (extend-env*
                              (map2 bind ns vals)
                              c-env)
                             next-k)]
              [contV (k-v) (if (or (empty? vals)
                                   (not (empty? (rest vals))))
                               (error 'interp "wrong arity")
                               (continue k-v (first vals)))]
              [else (error 'interp "not a function")])]
    [doSecondAvgK (m r env next-k)
                  (interp m env
                          (doThirdAvgK v r env next-k))]
    [doThirdAvgK (l r env next-k)
                 (interp r env
                         (doAverageK (num+ l v) next-k))]
    [doAverageK (sum1 next-k)
                (continue next-k (num/ (num+ sum1 v) (numV 3)))]
    [doNegateK (next-k)
               (continue next-k (num* v (numV -1)))]
    [doIf0K (thn els env next-k)
                (interp (if (num-zero? v) thn els) env next-k)]))

(define (bak-cons (el : 'a) (ls : (listof 'a))) : (listof 'a)
  (cond
    [(empty? ls) (list el)]
    [else (cons (first ls) (bak-cons el (rest ls)))]))

(module+ test
  (test (interp (parse '2) mt-env (doneK))
        (numV 2))
  (test/exn (interp (parse `x) mt-env (doneK))
            "free variable")
  (test (interp (parse `x)
                (extend-env (bind 'x (numV 9)) mt-env)
                (doneK))
        (numV 9))
  (test (interp (parse '{+ 2 1}) mt-env (doneK))
        (numV 3))
  (test (interp (parse '{* 2 1}) mt-env (doneK))
        (numV 2))
  (test (interp (parse '{+ {* 2 3} {+ 5 8}})
                mt-env
                (doneK))
        (numV 19))
  (test (interp (parse '{lambda {x} {+ x x}})
                mt-env
                (doneK))
        (closV (list 'x) (plusC (idC 'x) (idC 'x)) mt-env))
  (test (interp (parse '{let {[x 5]}
                          {+ x x}})
                mt-env
                (doneK))
        (numV 10))
  (test (interp (parse '{let {[x 5]}
                          {let {[x {+ 1 x}]}
                            {+ x x}}})
                mt-env
                (doneK))
        (numV 12))
  (test (interp (parse '{let {[x 5]}
                          {let {[y 6]}
                            x}})
                mt-env
                (doneK))
        (numV 5))
  (test (interp (parse '{{lambda {x} {+ x x}} 8})
                mt-env
                (doneK))
        (numV 16))

  (test (interp (parse '{let/cc k {+ 1 {k 0}}})
                mt-env
                (doneK))
        (numV 0))
  (test (interp (parse '{let {[f {let/cc k k}]}
                          {f {lambda {x} 10}}})
                mt-env
                (doneK))
        (numV 10))

  (test/exn (interp (parse '{1 2}) mt-env (doneK))
            "not a function")
  (test/exn (interp (parse '{+ 1 {lambda {x} x}}) mt-env (doneK))
            "not a number")
  (test/exn (interp (parse '{let {[bad {lambda {x} {+ x y}}]}
                              {let {[y 5]}
                                {bad 2}}})
                    mt-env
                    (doneK))
            "free variable")
  (test (interp (parse '{+ 4 {if0 1 2 3}}) mt-env (doneK))
        (numV 7))
  (test (interp (parse '{+ 4 {if0 0 2 3}}) mt-env (doneK))
        (numV 6))
  (test (interp (parse '{+ 2 {neg 5}}) mt-env (doneK))
        (numV -3))
  (test (interp (parse '{+ 2 {avg 5 7 9}}) mt-env (doneK))
        (numV 9))
  (test (interp (parse '{{lambda {x y z w} {+ x {+ y {* w z}}}} 1 2 3 4}) mt-env (doneK))
        (numV 15))
  (test (interp (parse '{{lambda {} 42}}) mt-env (doneK))
        (numV 42))
  (test/exn (interp (parse '{{let/cc k {k 3 4}}}) mt-env (doneK))
            "wrong arity")
  
  ;; Eager:
  (test/exn (interp (parse '{{lambda {x} 0} {1 2}}) mt-env (doneK))
            "not a function")

  (test (continue (doneK) (numV 5))
        (numV 5))
  (test (continue (addSecondK (numC 6) mt-env (doneK)) (numV 5))
        (numV 11))
  (test (continue (doAddK (numV 7) (doneK)) (numV 5))
        (numV 12))
  (test (continue (multSecondK (numC 6) mt-env (doneK)) (numV 5))
        (numV 30))
  (test (continue (doMultK (numV 7) (doneK)) (numV 5))
        (numV 35))
  (test (continue (appArgK (list (numC 5)) mt-env (doneK)) (closV (list 'x) (idC 'x) mt-env))
        (numV 5))
  (test (continue (doAppK (list (numV 8)) (doneK)) (closV (list 'x) (idC 'x) mt-env))
        (numV 8))
  (test (continue (doSecondAvgK (numC 2) (numC 3) mt-env (doneK)) (numV 1))
        (numV 2))
  (test (continue (doThirdAvgK (numV 2) (numC 2) mt-env (doneK)) (numV 8))
        (numV 4))
  (test (continue (doAverageK (numV 12) (doneK)) (numV 9))
        (numV 7))
  (test (continue (doNegateK (doneK)) (numV 2))
        (numV -2))
  (test (continue (doIf0K (numC 2) (numC 3) mt-env (doneK)) (numV 1))
        (numV 3))
  (test (continue (doIf0K (numC 2) (numC 3) mt-env (doneK)) (numV 0))
        (numV 2)))

;; interp-expr ------------------------------------------
(define (interp-expr (a : ExprC)) : s-expression
  (type-case Value (interp a mt-env (doneK))
    [numV (n) (number->s-exp n)]
    [else `function]))

(module+ test
  (test (interp-expr (parse '{lambda {x} 1}))
        `function)
  (test (interp-expr (parse '{neg 2}))
        '-2)
  (test (interp-expr (parse '{avg 0 6 6}))
        '4)
  (test (interp-expr (parse '{let/cc k {neg {k 3}}}))
        '3)
  (test (interp-expr (parse '{let/cc k {avg 0 {k 3} 0}}))
        '3)
  (test (interp-expr (parse '{let/cc k {avg {k 2} {k 3} 0}}))
        '2)
  (test (interp-expr (parse '{if0 1 2 3}))
        '3)
  (test (interp-expr (parse '{if0 0 2 3}))
        '2)
  (test (interp-expr (parse '{let/cc k {if0 {k 9} 2 3}}))
        '9)
  (test (interp-expr (parse '{{lambda {x y} {+ y {neg x}}} 10 12}))
        '2)
  (test (interp-expr (parse '{lambda {} 12}))
        `function)
  (test (interp-expr (parse '{lambda {x} {lambda {} x}}))
        `function)
  (test (interp-expr (parse '{{{lambda {x} {lambda {} x}} 13}}))
        '13)

  (test (interp-expr (parse '{let/cc esc {{lambda {x y} x} 1 {esc 3}}}))
        '3)
  (test (interp-expr (parse '{{let/cc esc {{lambda {x y} {lambda {z} {+ z y}}}
                                           1 
                                           {let/cc k {esc k}}}}
                              10}))
        '20))

;; num+ and num* ----------------------------------------
(define (num-op [op : (number number -> number)] [l : Value] [r : Value]) : Value
  (cond
   [(and (numV? l) (numV? r))
    (numV (op (numV-n l) (numV-n r)))]
   [else
    (error 'interp "not a number")]))
(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))
(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))
(define (num/ [l : Value] [r : Value]) : Value
  (num-op / l r))
(define (num-zero? (n : Value)) : boolean
  (if (numV? n)
      (eq? (numV-n n) 0)
      (error 'interp "not a number")))

(module+ test
  (test (num+ (numV 1) (numV 2))
        (numV 3))
  (test (num* (numV 2) (numV 3))
        (numV 6))
  (test (num/ (numV 2) (numV 2))
        (numV 1))
  (test (num-zero? (numV 1))
        #f)
  (test (num-zero? (numV 0))
        #t)
  (test/exn (num-zero? (contV (doneK)))
        "not a number"))

;; lookup ----------------------------------------
(define (lookup [n : symbol] [env : Env]) : Value
  (cond
   [(empty? env) (error 'lookup "free variable")]
   [else (cond
          [(symbol=? n (bind-name (first env)))
           (bind-val (first env))]
          [else (lookup n (rest env))])]))

(module+ test
  (test/exn (lookup 'x mt-env)
            "free variable")
  (test (lookup 'x (extend-env (bind 'x (numV 8)) mt-env))
        (numV 8))
  (test (lookup 'x (extend-env
                    (bind 'x (numV 9))
                    (extend-env (bind 'x (numV 8)) mt-env)))
        (numV 9))
  (test (lookup 'y (extend-env
                    (bind 'x (numV 9))
                    (extend-env (bind 'y (numV 8)) mt-env)))
        (numV 8)))
  