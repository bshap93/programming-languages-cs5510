#lang plai-typed
(require plai-typed/s-exp-match)

(define-type Value
  [numV (n : number)]
  [closV (arg : symbol)
         (body : ExprC)
         (env : Env)]
  [pairV (fst : Thunk)
         (snd : Thunk)])

(define-type Thunk
  [delay (body : ExprC)
         (env : Env)
         (done : (boxof (optionof Value)))])

(define-type ExprC
  [numC (n : number)]
  [idC (s : symbol)]
  [plusC (l : ExprC) 
         (r : ExprC)]
  [multC (l : ExprC)
         (r : ExprC)]
  [lamC (n : symbol)
        (body : ExprC)]
  [appC (fun : ExprC)
        (arg : ExprC)]
  [if0C (tst : ExprC)
        (thn : ExprC)
        (els : ExprC)]
  [pairC (f : ExprC)
        (l : ExprC)]
  [fstC (pr : ExprC)]
  [sndC (pr : ExprC)])

(define-type Binding
  [bind (name : symbol)
        (val : Thunk)])

(define-type-alias Env (listof Binding))

(define mt-env empty)
(define extend-env cons)

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
       (appC (lamC (s-exp->symbol (first bs))
                   (parse (third (s-exp->list s))))
             (parse (second bs))))]
    [(s-exp-match? '{lambda {SYMBOL} ANY} s)
     (lamC (s-exp->symbol (first (s-exp->list 
                                  (second (s-exp->list s)))))
           (parse (third (s-exp->list s))))]
    [(s-exp-match? '{if0 ANY ANY ANY} s)
     (if0C (parse (second (s-exp->list s)))
           (parse (third (s-exp->list s)))
           (parse (fourth (s-exp->list s))))]
    [(s-exp-match? '{pair ANY ANY} s)
     (pairC (parse (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
    [(s-exp-match? '{fst ANY} s)
     (fstC (parse (second (s-exp->list s))))]
    [(s-exp-match? '{snd ANY} s)
     (sndC (parse (second (s-exp->list s))))]
    [(s-exp-match? '{ANY ANY} s)
     (appC (parse (first (s-exp->list s)))
           (parse (second (s-exp->list s))))]
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
        (appC (lamC 'x (idC 'y))
              (plusC (numC 1) (numC 2))))
  (test (parse '{lambda {x} 9})
        (lamC 'x (numC 9)))
  (test (parse '{double 9})
        (appC (idC 'double) (numC 9)))
  (test/exn (parse '{{+ 1 2}})
            "invalid input")
  (test (parse '{if0 1 2 3})
        (if0C (numC 1) (numC 2) (numC 3)))
  (test (parse '{pair 1 2})
        (pairC (numC 1) (numC 2)))
  (test (parse '{fst {pair 1 2}})
        (fstC (pairC (numC 1) (numC 2))))
  (test (parse '{snd {pair 1 2}})
        (sndC (pairC (numC 1) (numC 2)))))

;; interp ----------------------------------------
(define (interp [a : ExprC] [env : Env]) : Value
  (type-case ExprC a
    [numC (n) (numV n)]
    [idC (s) (force (lookup s env))]
    [plusC (l r) (num+ (interp l env)
                       (interp r env))]
    [multC (l r) (num* (interp l env)
                       (interp r env))]
    [lamC (n body)
          (closV n body env)]
    [if0C (tst thn els)
          (interp (if (num-zero? (interp tst env))
                      thn
                      els)
                  env)]
    [pairC (f s) (pairV (delay f env (box (none)))
                        (delay s env (box (none))))]
    [fstC (pr) (extract-pair pr #t env)]
    [sndC (pr) (extract-pair pr #f env)]
    [appC (fun arg) (type-case Value (interp fun env)
                      [closV (n body c-env)
                             (interp body
                                     (extend-env
                                      (bind n (delay arg env (box (none))))
                                      c-env))]
                      [else (error 'interp "not a function")])]))

(module+ test
  (test (interp (parse '2) mt-env)
        (numV 2))
  (test/exn (interp (parse `x) mt-env)
            "free variable")
  (test (interp (parse `x) 
                (extend-env (bind 'x (delay (numC 9) mt-env (box (none)))) mt-env))
        (numV 9))
  (test (interp (parse '{+ 2 1}) mt-env)
        (numV 3))
  (test (interp (parse '{* 2 1}) mt-env)
        (numV 2))
  (test (interp (parse '{+ {* 2 3} {+ 5 8}})
                mt-env)
        (numV 19))
  (test (interp (parse '{lambda {x} {+ x x}})
                mt-env)
        (closV 'x (plusC (idC 'x) (idC 'x)) mt-env))
  (test (interp (parse '{let {[x 5]}
                          {+ x x}})
                mt-env)
        (numV 10))
  (test (interp (parse '{let {[x 5]}
                          {let {[x {+ 1 x}]}
                            {+ x x}}})
                mt-env)
        (numV 12))
  (test (interp (parse '{let {[x 5]}
                         {let {[y 6]}
                          x}})
                mt-env)
        (numV 5))
  (test (interp (parse '{{lambda {x} {+ x x}} 8})
                mt-env)
        (numV 16))

  (test (interp (parse '{{lambda {x} 5} {1 2}})
                 mt-env)
        (numV 5))

  (test/exn (interp (parse '{1 2}) mt-env)
            "not a function")
  (test/exn (interp (parse '{+ 1 {lambda {x} x}}) mt-env)
            "not a number")
  (test/exn (interp (parse '{let {[bad {lambda {x} {+ x y}}]}
                              {let {[y 5]}
                                {bad 2}}})
                    mt-env)
            "free variable")
  
  (test (interp (parse '{if0 0 1 2}) mt-env)
        (numV 1))
  (test (interp (parse '{if0 1 1 2}) mt-env)
        (numV 2))
  (test (interp (parse '{pair 1 2}) mt-env)
        (pairV (delay (numC 1) mt-env (box (none)))
               (delay (numC 2) mt-env (box (none)))))
  (test (interp (parse '{fst {pair 1 2}}) mt-env)
        (numV 1))
  (test (interp (parse '{snd {pair 1 2}}) mt-env)
        (numV 2))
  
  ;; Lazy evaluation:
  (test (interp (parse '{{lambda {x} 0}
                         {+ 1 {lambda {y} y}}})
                mt-env)
        (numV 0))
  (test (interp (parse '{let {[x {+ 1 {lambda {y} y}}]}
                          0})
                mt-env)
        (numV 0))
  (test (interp (parse '{fst {pair 3
                                   {+ 1 {lambda {y} y}}}})
                mt-env)
        (numV 3))
  (test (interp (parse '{snd {pair {+ 1 {lambda {y} y}}
                                   4}})
                mt-env)
        (numV 4))
  (test (interp (parse '{fst {pair 5
                                   ;; Infinite loop:
                                   {{lambda {x} {x x}}
                                    {lambda {x} {x x}}}}})
                mt-env)
        (numV 5))
  
  (test (interp
         (parse 
          '{let {[mkrec
                  ;; This is call-by-name mkrec
                  ;;  (simpler than call-by-value):
                  {lambda {body-proc}
                    {let {[fX {lambda {fX}
                                {body-proc {fX fX}}}]}
                      {fX fX}}}]}
             {let {[fib
                    {mkrec
                     {lambda {fib}
                       ;; Fib:
                       {lambda {n}
                         {if0 n
                              1
                              {if0 {+ n -1}
                                   1
                                   {+ {fib {+ n -1}}
                                      {fib {+ n -2}}}}}}}}]}
               ;; Call fib on 4:
               {fib 4}}})
         mt-env)
        (numV 5))

  (test (interp
         (parse 
          '{let {[mkrec
                  ;; This is call-by-name mkrec
                  ;;  (simpler than call-by-value):
                  {lambda {body-proc}
                    {let {[fX {lambda {fX}
                                {body-proc {fX fX}}}]}
                      {fX fX}}}]}
             {let {[nats-from
                    {mkrec
                     {lambda {nats-from}
                       ;; nats-from:
                       {lambda {n}
                         {pair n {nats-from {+ n 1}}}}}}]}
               {let {[list-ref
                      {mkrec
                       {lambda {list-ref}
                         ;; list-ref:
                         {lambda {n}
                           {lambda {l}
                             {if0 n
                                  {fst l}
                                  {{list-ref {+ n -1}} {snd l}}}}}}}]}
                 ;; Call list-ref on infinite list:
                 {{list-ref 4} {nats-from 2}}}}})
         mt-env)
        (numV 6))

  #;
  (time (interp (parse '{let {[x2 {lambda {n} {+ n n}}]}
                          {let {[x4 {lambda {n} {x2 {x2 n}}}]}
                            {let {[x16 {lambda {n} {x4 {x4 n}}}]}
                              {let {[x256 {lambda {n} {x16 {x16 n}}}]}
                                {let {[x65536 {lambda {n} {x256 {x256 n}}}]}
                                  {x65536 1}}}}}})
                mt-env)))

;; interp-expr ----------------------------------

(define (interp-expr [a : ExprC]) : s-expression
  (type-case Value (interp a mt-env)
    [numV (n) (number->s-exp n)]
    [closV (a b c) `function]
    [pairV (f s) `pair]))

(module+ test
  (test (interp-expr (parse '{lambda {x} {+ x 1}}))
        `function)
  (test (interp-expr (parse '10))
        '10)
  (test (interp-expr (parse '{+ 10 17}))
        '27)
  (test (interp-expr (parse '{* 10 7}))
        '70)
  (test (interp-expr (parse '{{lambda {x} {+ x 12}}
                              {+ 1 17}}))
        '30)
  
  (test (interp-expr (parse '{let {[x 0]}
                               {let {[f {lambda {y} {+ x y}}]}
                                 {+ {f 1}
                                    {let {[x 3]}
                                      {f 2}}}}}))
        '3)
  
  (test (interp-expr (parse '{if0 0 1 2}))
        '1)
  (test (interp-expr (parse '{if0 1 1 2}))
        '2)
  
  (test (interp-expr (parse '{pair 1 2}))
        `pair)
  (test (interp-expr (parse '{fst {pair 1 2}}))
        '1)
  (test (interp-expr (parse '{snd {pair 1 2}}))
        '2)
  
  ;; Lazy evaluation:
  (test (interp-expr (parse '{{lambda {x} 0}
                              {+ 1 {lambda {y} y}}}))
        '0)
  (test (interp-expr (parse '{let {[x {+ 1 {lambda {y} y}}]}
                               0}))
        '0)
  (test (interp-expr (parse '{fst {pair 3
                                        {+ 1 {lambda {y} y}}}}))
        '3)
  (test (interp-expr (parse '{snd {pair {+ 1 {lambda {y} y}}
                                        4}}))
        '4)
  (test (interp-expr (parse '{fst {pair 5
                                        ;; Infinite loop:
                                        {{lambda {x} {x x}}
                                         {lambda {x} {x x}}}}}))
        '5)
  
  (test (interp-expr 
         (parse 
          '{let {[mkrec
                  ;; This is call-by-name mkrec
                  ;;  (simpler than call-by-value):
                  {lambda {body-proc}
                    {let {[fX {lambda {fX}
                                {body-proc {fX fX}}}]}
                      {fX fX}}}]}
              {let {[fib
                     {mkrec
                      {lambda {fib}
                        ;; Fib:
                        {lambda {n}
                          {if0 n
                               1
                               {if0 {+ n -1}
                                    1
                                    {+ {fib {+ n -1}}
                                       {fib {+ n -2}}}}}}}}]}
                ;; Call fib on 4:
                {fib 4}}}))
        '5)

  (test (interp-expr 
         (parse 
          '{let {[mkrec
                  ;; This is call-by-name mkrec
                  ;;  (simpler than call-by-value):
                  {lambda {body-proc}
                    {let {[fX {lambda {fX}
                                {body-proc {fX fX}}}]}
                      {fX fX}}}]}
             {let {[nats-from
                    {mkrec
                     {lambda {nats-from}
                       ;; nats-from:
                       {lambda {n}
                         {pair n {nats-from {+ n 1}}}}}}]}
               {let {[list-ref
                      {mkrec
                       {lambda {list-ref}
                         ;; list-ref:
                         {lambda {n}
                           {lambda {l}
                             {if0 n
                                  {fst l}
                                  {{list-ref {+ n -1}} {snd l}}}}}}}]}
                 ;; Call list-ref on infinite list:
                 {{list-ref 4} {nats-from 2}}}}}))
        '6))

;; force ----------------------------------------

(define (force [t : Thunk]) : Value
  (type-case Thunk t
    [delay (b e d) (type-case (optionof Value) (unbox d)
                     [none ()
                           (let ([v (interp b e)])
                             (begin
                               (set-box! d (some v))
                               v))]
                     [some (v) v])]))

(module+ test
  (test (force (delay (numC 8) mt-env (box (none))))
        (numV 8))
  (test (let ([v (delay (numC 8) mt-env (box (none)))])
          (begin
            (force v)
            (force v)))
        (numV 8))
  (test (force (delay (numC 8) mt-env (box (some (numV 9)))))
        (numV 9))
  (test (force (delay (idC 'x)
                      (extend-env (bind 'x (delay (numC 9) mt-env (box (none))))
                                  mt-env)
                      (box (none))))
        (numV 9)))

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
(define (num-zero? [v : Value]) : boolean
  (type-case Value v
    [numV (n) (zero? n)]
    [else (error 'interp "not a number")]))

(module+ test
  (test (num+ (numV 1) (numV 2))
        (numV 3))
  (test (num* (numV 2) (numV 3))
        (numV 6))
  (test (num-zero? (numV 0))
        #t)
  (test (num-zero? (numV 1))
        #f)
  (test/exn (num-zero? (closV 'x (numC 1) mt-env))
        "not a number"))

;; lookup ----------------------------------------
(define (lookup [n : symbol] [env : Env]) : Thunk
  (cond
   [(empty? env) (error 'lookup "free variable")]
   [else (cond
          [(symbol=? n (bind-name (first env)))
           (bind-val (first env))]
          [else (lookup n (rest env))])]))

(module+ test
  (test/exn (lookup 'x mt-env)
            "free variable")
  (test (lookup 'x (extend-env (bind 'x (delay (numC 8) mt-env (box (none)))) mt-env))
        (delay (numC 8) mt-env (box (none))))
  (test (lookup 'x (extend-env
                    (bind 'x (delay (numC 9) mt-env (box (none))))
                    (extend-env (bind 'x (delay (numC 8) mt-env (box (none)))) mt-env)))
        (delay (numC 9) mt-env (box (none))))
  (test (lookup 'y (extend-env
                    (bind 'x (delay (numC 9) mt-env (box (none))))
                    (extend-env (bind 'y (delay (numC 8) mt-env (box (none)))) mt-env)))
        (delay (numC 8) mt-env (box (none)))))

;; extract-pair ----------------------------------
(define (extract-pair [pr : ExprC] [fst? : boolean] [env : Env]) : Value
  (type-case Value (interp pr env)
    [pairV (f s) (if fst?
                     (force f)
                     (force s))]
    [else (error 'interp "not a pair")]))

(module+ test
  (test (extract-pair (pairC (numC 1) (numC 2)) #t mt-env)
        (numV 1))
  (test (extract-pair (pairC (numC 1) (numC 2)) #f mt-env)
        (numV 2))
  (test/exn (extract-pair (numC 1) #t mt-env)
            "not a pair"))