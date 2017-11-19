#lang plai-typed
(require plai-typed/s-exp-match)

(define-type Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [pairV (l : Value)
         (r : Value)]
  [closV (args : (listof symbol))
         (body : ExprC)
         (env : Env)])

(define-type ExprC
  [numC (n : number)]
  [boolC (b : boolean)]
  [idC (s : symbol)]
  [=C (l : ExprC)
      (r : ExprC)]
  [ifC (tst : ExprC)
       (thn : ExprC)
       (els : ExprC)]
  [plusC (l : ExprC) 
         (r : ExprC)]
  [multC (l : ExprC)
         (r : ExprC)]
  [lamC (ns : (listof symbol))
        (arg-types : (listof Type))
        (body : ExprC)]
  [appC (fun : ExprC)
        (args : (listof ExprC))]
  [pairC (l : ExprC)
         (r : ExprC)]
  [fstC (p : ExprC)]
  [rstC (p : ExprC)])

(define-type Type
  [numT]
  [boolT]
  [arrowT (args : (listof Type))
          (result : Type)]
  [crossT (l : Type)
          (r : Type)])

(define-type Binding
  [bind (name : symbol)
        (val : Value)])

(define-type-alias Env (listof Binding))

(define-type TypeBinding
  [tbind (name : symbol)
         (type : Type)])

(define-type-alias TypeEnv (listof TypeBinding))

(define mt-env empty)
(define extend-env cons)
(define extend-env* append)

(module+ test
  (print-only-errors true))

;; parse ----------------------------------------
(define (parse [s : s-expression]) : ExprC
  (cond
    [(s-exp-match? `true s) (boolC #t)]
    [(s-exp-match? `false s) (boolC #f)]
    [(s-exp-match? `NUMBER s) (numC (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idC (s-exp->symbol s))]
    [(s-exp-match? '{= ANY ANY} s)
     (=C (parse (second (s-exp->list s)))
         (parse (third (s-exp->list s))))]
    [(s-exp-match? '{if ANY ANY ANY} s)
     (ifC (parse (second (s-exp->list s)))
          (parse (third (s-exp->list s)))
          (parse (fourth (s-exp->list s))))]
    [(s-exp-match? '{pair ANY ANY} s)
     (pairC (parse (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
    [(s-exp-match? '{fst ANY} s)
     (fstC (parse (second (s-exp->list s))))]
    [(s-exp-match? '{rst ANY} s)
     (rstC (parse (second (s-exp->list s))))]
    [(s-exp-match? '{+ ANY ANY} s)
     (plusC (parse (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
    [(s-exp-match? '{* ANY ANY} s)
     (multC (parse (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
    [(s-exp-match? '{let {[SYMBOL : ANY ANY]} ANY} s)
     (let ([bs (s-exp->list (first
                             (s-exp->list (second
                                           (s-exp->list s)))))])
       (appC (lamC (list (s-exp->symbol (first bs)))
                   (list (parse-type (third bs)))
                   (parse (third (s-exp->list s))))
             (list (parse (fourth bs)))))]
    [(s-exp-match? '{lambda {[SYMBOL : ANY] ...} ANY} s)
     (let ([args (map s-exp->list (s-exp->list (second (s-exp->list s))))])
       (lamC (map s-exp->symbol (map first args))
             (map parse-type (map third args))
             (parse (third (s-exp->list s)))))]
    [(s-exp-match? '{ANY ANY ...} s)
     (appC (parse (first (s-exp->list s)))
           (map parse (rest (s-exp->list s))))]
    [else (error 'parse "invalid input")]))

(define (parse-type [s : s-expression]) : Type
  (cond
   [(s-exp-match? `num s) 
    (numT)]
   [(s-exp-match? `bool s)
    (boolT)]
   [(s-exp-match? `(ANY ... -> ANY) s)
    (let ([split (get-arrow-args (s-exp->list s))])
      (arrowT (map parse-type (first split))
              (parse-type (first (second split)))))]
   [(s-exp-match? `(ANY * ANY) s)
    (crossT (parse-type (first (s-exp->list s)))
            (parse-type (third (s-exp->list s))))]
   [else (error 'parse-type "invalid input")]))

(define (get-arrow-args [lst : (listof s-expression)]) : (listof (listof s-expression))
  (foldr (lambda (el next)
           (if (equal? el `->)
               (cons empty next)
               (cons (cons el (first next)) (rest next))))
         (list empty) lst))

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
  (test (parse '{let {[x : num {+ 1 2}]}
                  y})
        (appC (lamC (list 'x) (list (numT)) (idC 'y))
              (list (plusC (numC 1) (numC 2)))))
  (test (parse '{lambda {[x : num]} 9})
        (lamC (list 'x) (list (numT)) (numC 9)))
  (test (parse '{double 9})
        (appC (idC 'double) (list (numC 9))))
  (test (parse `true)
        (boolC #t))
  (test (parse `false)
        (boolC #f))
  (test (parse '{= 1 1})
        (=C (numC 1) (numC 1)))
  (test (parse '{if true 2 3})
        (ifC (boolC #t) (numC 2) (numC 3)))
  (test (parse '{pair 1 2})
        (pairC (numC 1) (numC 2)))
  (test (parse '{fst 1})
        (fstC (numC 1)))
  (test (parse '{rst 1})
        (rstC (numC 1)))
  #;; Commented because this is now valid input (with zero-arg functions)
  (test/exn (parse '{{+ 1 2}})
            "invalid input")
  (test/exn (parse '{{}})
            "invalid input")

  (test (parse-type `num)
        (numT))
  (test (parse-type `bool)
        (boolT))
  (test (parse-type `(num -> bool))
        (arrowT (list (numT)) (boolT)))
  (test (parse-type `(-> bool))
        (arrowT empty (boolT)))
  (test (parse-type `(num bool -> bool))
        (arrowT (list (numT) (boolT)) (boolT)))
  (test (parse-type `(num * bool))
        (crossT (numT) (boolT)))
  (test/exn (parse-type '1)
            "invalid input"))

;; interp ----------------------------------------
(define (interp [a : ExprC] [env : Env]) : Value
  (type-case ExprC a
    [numC (n) (numV n)]
    [boolC (b) (boolV b)]
    [=C (l r) (boolV (equal? (interp l env) (interp r env)))]
    [ifC (tst thn els) (type-case Value (interp tst env)
                         [boolV (b) (if b
                                        (interp thn env)
                                        (interp els env))]
                         [else (error 'interp "not a boolean")])]
    [idC (s) (lookup s env)]
    [plusC (l r) (num+ (interp l env) (interp r env))]
    [multC (l r) (num* (interp l env) (interp r env))]
    [pairC (l r) (pairV (interp l env) (interp r env))]
    [fstC (p) (extract-pair p env #t)]
    [rstC (p) (extract-pair p env #f)]
    [lamC (ns ts body)
          (closV ns body env)]
    [appC (fun args) (type-case Value (interp fun env)
                       [closV (ns body c-env)
                              (interp body
                                      (extend-env*
                                       (map2 bind ns (interp-args args env))
                                       c-env))]
                       [else (error 'interp "not a function")])]))

(define (interp-args [args : (listof ExprC)] [env : Env]) : (listof Value)
  (if (empty? args)
      empty
      (cons (interp (first args) env)
            (interp-args (rest args) env))))

(define (extract-pair [p : ExprC] [env : Env] [first : boolean]) : Value
  (type-case Value (interp p env)
    [pairV (l r) (if first l r)]
    [else (error 'interp "not a pair")]))

(module+ test
  (test (interp (parse '2) mt-env)
        (numV 2))
  (test/exn (interp (parse `x) mt-env)
            "free variable")
  (test (interp (parse `x) 
                (extend-env (bind 'x (numV 9)) mt-env))
        (numV 9))
  (test (interp (parse '{+ 2 1}) mt-env)
        (numV 3))
  (test (interp (parse '{* 2 1}) mt-env)
        (numV 2))
  (test (interp (parse '{+ {* 2 3} {+ 5 8}})
                mt-env)
        (numV 19))
  (test (interp (parse '{lambda {[x : num]} {+ x x}})
                mt-env)
        (closV (list 'x) (plusC (idC 'x) (idC 'x)) mt-env))
  (test (interp (parse '{let {[x : num 5]}
                          {+ x x}})
                mt-env)
        (numV 10))
  (test (interp (parse '{let {[x : num 5]}
                          {let {[x : num {+ 1 x}]}
                            {+ x x}}})
                mt-env)
        (numV 12))
  (test (interp (parse '{let {[x : num 5]}
                          {let {[y : num 6]}
                            x}})
                mt-env)
        (numV 5))
  (test (interp (parse '{{lambda {[x : num]} {+ x x}} 8})
                mt-env)
        (numV 16))
  (test (interp (parse '{pair 10 8})
                mt-env)
        (pairV (numV 10) (numV 8)))
  
  (test (interp (parse '{fst {pair 10 8}})
                mt-env)
        (numV 10))
  
  (test (interp (parse '{rst {pair 10 8}})
                mt-env)
        (numV 8))

  (test/exn (interp (parse '{fst 1}) mt-env)
            "not a pair")
  (test/exn (interp (parse '{1 2}) mt-env)
            "not a function")
  (test/exn (interp (parse '{+ 1 {lambda {[x : num]} x}}) mt-env)
            "not a number")
  (test/exn (interp (parse '{let {[bad : (num -> num) {lambda {[x : num]} {+ x y}}]}
                              {let {[y : num 5]}
                                {bad 2}}})
                    mt-env)
            "free variable")
  (test (interp (parse '{if {= 13 {if {= 1 {+ -1 2}}
                                      12
                                      13}}
                            4
                            5})
                mt-env)
         (numV 5))
  (test (interp (parse '{if {= 13 {+ 1 12}}
                            true
                            false})
                mt-env)
        (boolV #t))
  (test (interp (parse '{if {= 13 {+ 1 1}}
                            true
                            false})
                mt-env)
        (boolV #f))
  (test/exn (interp (parse '{if 1 2 3})
                    mt-env)
            "not a boolean")
  (test (interp (parse '{{lambda {}
                           10}})
                mt-env)
        (numV 10))
  
  (test (interp (parse '{{lambda {[x : num] [y : num]} {+ x y}}
                         10
                         20})
                mt-env)
        (numV 30)))

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

(module+ test
  (test (num+ (numV 1) (numV 2))
        (numV 3))
  (test (num* (numV 2) (numV 3))
        (numV 6)))

;; lookup ----------------------------------------
(define (make-lookup [name-of : ('a -> symbol)] [val-of : ('a -> 'b)])
  (lambda ([name : symbol] [vals : (listof 'a)]) : 'b
    (cond
     [(empty? vals)
      (error 'find "free variable")]
     [else (if (equal? name (name-of (first vals)))
               (val-of (first vals))
               ((make-lookup name-of val-of) name (rest vals)))])))

(define lookup
  (make-lookup bind-name bind-val))

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

;; typecheck ----------------------------------------
(define (typecheck [a : ExprC] [tenv : TypeEnv])
  (type-case ExprC a
    [numC (n) (numT)]
    [boolC (b) (boolT)]
    [=C (l r)
        (begin
          (typecheck l tenv)
          (typecheck r tenv)
          (boolT))]
    [ifC (tst thn els)
         (type-case Type (typecheck tst tenv)
           [boolT () (let ([thn-type (typecheck thn tenv)])
                       (let ([els-type (typecheck els tenv)])
                         (if (equal? thn-type els-type)
                             thn-type
                             (type-error thn-type (to-string els-type)))))]
           [else (type-error tst "boolean")])]
    [plusC (l r) (typecheck-nums l r tenv)]
    [multC (l r) (typecheck-nums l r tenv)]
    [pairC (l r) (crossT (typecheck l tenv) (typecheck r tenv))]
    [fstC (p) (extract-pair-type p tenv #t)]
    [rstC (p) (extract-pair-type p tenv #f)]
    [idC (n) (type-lookup n tenv)]
    [lamC (ns arg-types body)
          (arrowT arg-types
                  (typecheck body 
                             (extend-env*
                              (map2 tbind ns arg-types)
                              tenv)))]
    [appC (fun args)
          (type-case Type (typecheck fun tenv)
            [arrowT (arg-types result-type)
                    (typecheck-func args arg-types tenv result-type)]
            [else (type-error fun "function")])]))

(define (typecheck-func args arg-types tenv result-type)
  (cond
    [(and (empty? args) (empty? arg-types))
     result-type]
    [(or (empty? args) (empty? arg-types))
     (error 'typecheck "wrong arity")]
    [(equal? (first arg-types) (typecheck (first args) tenv))
     (typecheck-func (rest args) (rest arg-types) tenv result-type)]
    [else (type-error (first args) (to-string (first arg-types)))]))

(define (extract-pair-type [p : ExprC] [tenv : TypeEnv] [first : boolean])
  (type-case Type (typecheck p tenv)
    [crossT (l r) (if first l r)]
    [else (type-error p "pair")]))

(define (typecheck-nums l r tenv)
  (type-case Type (typecheck l tenv)
    [numT ()
          (type-case Type (typecheck r tenv)
            [numT () (numT)]
            [else (type-error r "num")])]
    [else (type-error l "num")]))

(define (type-error a msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string a)
                      (string-append " not "
                                     msg)))))

(define type-lookup
  (make-lookup tbind-name tbind-type))

(module+ test
  (test (typecheck (parse '10) mt-env)
        (numT))
  (test (typecheck (parse '{+ 10 17}) mt-env)
        (numT))
  (test (typecheck (parse '{* 10 17}) mt-env)
        (numT))
  (test (typecheck (parse '{lambda {[x : num]} 12}) mt-env)
        (arrowT (list (numT)) (numT)))
  (test (typecheck (parse '{lambda {[x : num]} {lambda {[y : bool]} x}}) mt-env)
        (arrowT (list (numT)) (arrowT (list (boolT))  (numT))))

  (test (typecheck (parse '{{lambda {[x : num]} 12}
                            {+ 1 17}})
                   mt-env)
        (numT))

  (test (typecheck (parse '{let {[x : num 4]}
                             {let {[f : (num -> num)
                                      {lambda {[y : num]} {+ x y}}]}
                               {f x}}})
                   mt-env)
        (numT))
  (test (typecheck (parse '{= 13 {if {= 1 {+ -1 2}}
                                     12
                                     13}})
                   mt-env)
         (boolT))
  (test (typecheck (parse '{pair 10 8})
                   mt-env)
        (crossT (numT) (numT)))
  
  (test (typecheck (parse '{fst {pair 10 8}})
                   mt-env)
        (numT))
  
  (test (typecheck (parse '{+ 1 {rst {pair 10 8}}})
                   mt-env)
        (numT))
  
  (test (typecheck (parse '{lambda {[x : (num * bool)]}
                             {fst x}})
                   mt-env)
        (arrowT (list (crossT (numT) (boolT))) (numT)))
  
  (test (typecheck (parse '{{lambda {[x : (num * bool)]}
                              {fst x}}
                            {pair 1 false}})
                   mt-env)
        (numT))
  
  (test (typecheck (parse '{{lambda {[x : (num * bool)]}
                              {rst x}}
                            {pair 1 false}})
                   mt-env)
        (boolT))
  
  (test/exn (typecheck (parse '{fst 10})
                       mt-env)
            "no type")
  
  (test/exn (typecheck (parse '{+ 1 {fst {pair false 8}}})
                       mt-env)
            "no type")
  
  (test/exn (typecheck (parse '{lambda {[x : (num * bool)]}
                                 {if {fst x}
                                     1
                                     2}})
                       mt-env)
            "no type")
  
  (test/exn (typecheck (parse '{+ 1 {if true true false}})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse '{1 2})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse '{{lambda {[x : bool]} x} 2})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse '{+ 1 {lambda {[x : num]} x}})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse '{* {lambda {[x : num]} x} 1})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse '{if 1 2 3})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse '{if true 1 false})
                       mt-env)
            "no type")
  (test (typecheck (parse '{{lambda {[x : num] [y : bool]} y}
                            10
                            false})
                   mt-env)
        (boolT))
  
  (test/exn (typecheck (parse '{{lambda {[x : num] [y : bool]} y}
                                false
                                10})
                       mt-env)
            "no type")
  (test/exn (typecheck (parse '{{lambda {} 3} 2}) mt-env)
            "wrong arity"))