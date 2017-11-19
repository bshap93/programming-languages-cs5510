#lang plai-typed
(require plai-typed/s-exp-match)

;; ============================================================
;; classes without inheritance

(define-type ExprC
  [numC (n : number)]
  [plusC (lhs : ExprC)
         (rhs : ExprC)]
  [multC (lhs : ExprC)
         (rhs : ExprC)]
  [argC]
  [thisC]
  [newC (class-name : symbol)
        (args : (listof ExprC))]
  [getC (obj-expr : ExprC)
        (field-name : symbol)]
  [sendC (obj-expr : ExprC)
         (method-name : symbol)
         (arg-expr : ExprC)]
  [ssendC (obj-expr : ExprC)
          (class-name : symbol)
          (method-name : symbol)
          (arg-expr : ExprC)]
  [selectC (num : ExprC)
           (obj-expr : ExprC)]
  [instanceofC (obj-expr : ExprC)
               (ancestor-name : symbol)])

(define-type ClassC
  [classC (name : symbol)
          (super-name : symbol)
          (field-names : (listof symbol))
          (methods : (listof MethodC))])

(define-type MethodC
  [methodC (name : symbol)
           (body-expr : ExprC)])

(define-type Value
  [numV (n : number)]
  [objV (class-name : symbol)
        (field-values : (listof Value))])

(module+ test
  (print-only-errors true))

;; ----------------------------------------

(define base-object (classC 'object 'object empty empty))

(define (make-find [name-of : ('a -> symbol)])
  (lambda ([name : symbol] [vals : (listof 'a)]) : 'a
          (cond
           [(empty? vals)
            (error 'find "not found")]
           [else (if (equal? name (name-of (first vals)))
                     (first vals)
                     ((make-find name-of) name (rest vals)))])))

(define (find-class [name : symbol] [classes : (listof ClassC)]) : ClassC
  (if (equal? name 'object)
      base-object
      ((make-find classC-name) name classes)))

(define find-method : (symbol (listof MethodC) -> MethodC)
  (make-find methodC-name))

;; A non-list pair:
(define-type (Pair 'a 'b)
  [kons (first : 'a) (rest : 'b)])

(define (get-field [name : symbol] 
                   [field-names : (listof symbol)] 
                   [vals : (listof Value)])
  ;; Pair fields and values, find by field name,
  ;; then extract value from pair
  (kons-rest ((make-find kons-first)
              name
              (map2 kons field-names vals))))

(module+ test
  (test/exn (find-class 'a empty)
            "not found")
  (test (find-class 'a (list (classC 'a 'object empty empty)))
        (classC 'a 'object empty empty))
  (test (find-class 'b (list (classC 'a 'object empty empty)
                             (classC 'b 'object empty empty)))
        (classC 'b 'object empty empty))
  (test (find-class 'object empty)
        base-object)
  (test (get-field 'a 
                   (list 'a 'b)
                   (list (numV 0) (numV 1)))
        (numV 0)))

;; ----------------------------------------

(define interp : (ExprC (listof ClassC) Value Value -> Value)
  (lambda (a classes this-val arg-val)
    (local [(define (recur expr)
              (interp expr classes this-val arg-val))]
      (type-case ExprC a
        [numC (n) (numV n)]
        [plusC (l r) (num+ (recur l) (recur r))]
        [multC (l r) (num* (recur l) (recur r))]
        [thisC () this-val]
        [argC () arg-val]
        [newC (class-name field-exprs)
              (local [(define c (find-class class-name classes))
                      (define vals (map recur field-exprs))]
                (if (= (length vals) (length (classC-field-names c)))
                    (objV class-name vals)
                    (error 'interp "wrong field count")))]
        [getC (obj-expr field-name)
              (type-case Value (recur obj-expr)
                [objV (class-name field-vals)
                      (type-case ClassC (find-class class-name classes)
                        [classC (name super-name field-names methods)
                                (get-field field-name field-names 
                                           field-vals)])]
                [else (error 'find "not found")])] ;; numbers dont have fields
        [sendC (obj-expr method-name arg-expr)
               (local [(define obj (recur obj-expr))
                       (define arg-val (recur arg-expr))]
                 (type-case Value obj
                   [objV (class-name field-vals)
                         (call-method class-name method-name classes
                                      obj arg-val)]
                   [numV (n)
                         (call-num-method method-name classes
                                          obj arg-val)]))]
        [ssendC (obj-expr class-name method-name arg-expr)
                (local [(define obj (recur obj-expr))
                        (define arg-val (recur arg-expr))]
                  (call-method class-name method-name classes
                               obj arg-val))]
        [selectC (num obj-expr)
                 (type-case Value (recur num)
                   [numV (n) (inner-select (numV n) (recur obj-expr) classes)]
                   [else (error 'interp "not a number")])]
        [instanceofC (obj-expr ancestor-name)
                     (local [(define obj (recur obj-expr))]
                       (type-case Value obj
                         [objV (class-name field-vals)
                               (if (is-instance class-name ancestor-name classes)
                                   (numV 0)
                                   (numV 1))]
                         [else (if (equal? ancestor-name 'object) ;; numbers belong to an unnamed subclass of object
                                   (numV 0)
                                   (numV 1))]))]))))

(define (is-instance [class-name : symbol] [ancestor-name : symbol] [classes : (listof ClassC)]) : boolean
  (cond
    [(equal? class-name ancestor-name) #t]
    [(equal? class-name 'object) #f]
    [else (type-case ClassC (find-class class-name classes)
            [classC (name super-name field-names methods)
                    (is-instance super-name ancestor-name classes)])]))

(define (call-method class-name method-name classes
                     obj arg-val)
  (type-case ClassC (find-class class-name classes)
    [classC (name super-name field-names methods)
            (type-case MethodC (find-method method-name methods)
              [methodC (name body-expr)
                       (interp body-expr
                               classes
                               obj
                               arg-val)])]))

(define (call-num-method method-name classes
                         num-val arg-val)
  (cond
    [(equal? method-name 'plus) (type-case Value arg-val
                                  [objV (class-name field-vals)
                                        (call-method class-name method-name classes arg-val num-val)]
                                  [numV (n) (num+ num-val arg-val)])]
    [(equal? method-name 'mult) (type-case Value arg-val
                                  [objV (class-name field-vals)
                                        (call-method class-name method-name classes arg-val num-val)]
                                  [numV (n) (num* num-val arg-val)])]
    [(equal? method-name 'select) (inner-select num-val arg-val classes)]
    [else (error 'find "not found")]))

(define (inner-select num-val arg-val classes)
  (type-case Value arg-val
    [objV (class-name field-vals)
          (if (equal? (numV-n num-val) 0)
              (call-method class-name 'zero classes arg-val (numV 0))
              (call-method class-name 'nonzero classes arg-val (numV 0)))]
    [else (error 'find "not found")])) ;; numbers dont have 'zero/'nonzero methods

(define (num-op [op : (number number -> number)]
                [op-name : symbol] 
                [x : Value]
                [y : Value]) : Value
  (cond
    [(and (numV? x) (numV? y))
     (numV (op (numV-n x) (numV-n y)))]
    [else (error 'interp "not a number")]))

(define (num+ x y) (num-op + '+ x y))
(define (num* x y) (num-op * '* x y))

;; ----------------------------------------
;; Examples

(module+ test
  (define posn-class
    (classC 
     'posn
     'object
     (list 'x 'y)
     (list (methodC 'mdist
                    (plusC (getC (thisC) 'x) (getC (thisC) 'y)))
           (methodC 'addDist
                    (plusC (sendC (thisC) 'mdist (numC 0))
                           (sendC (argC) 'mdist (numC 0))))
           (methodC 'addX
                    (plusC (getC (thisC) 'x) (argC)))
           (methodC 'multY (multC (argC) (getC (thisC) 'y)))
           (methodC 'factory12 (newC 'posn (list (numC 1) (numC 2)))))))

  (define posn3D-class
    (classC 
     'posn3D
     'posn
     (list 'x 'y 'z)
     (list (methodC 'mdist (plusC (getC (thisC) 'z)
                                  (ssendC (thisC) 'posn 'mdist (argC))))
           (methodC 'addDist (ssendC (thisC) 'posn 'addDist (argC))))))

  (define posn27 (newC 'posn (list (numC 2) (numC 7))))
  (define posn531 (newC 'posn3D (list (numC 5) (numC 3) (numC 1))))

  (define select-test-class
    (classC
     'selclass
     'object
     empty
     (list (methodC 'zero (argC))
           (methodC 'nonzero (numC 3)))))

  (define (interp-posn a)
    (interp a (list posn-class posn3D-class) (numV -1) (numV -1))))

;; ----------------------------------------

(module+ test
  (test (interp (numC 10) 
                empty (numV -1) (numV -1))
        (numV 10))
  (test (interp (plusC (numC 10) (numC 17))
                empty (numV -1) (numV -1))
        (numV 27))
  (test (interp (multC (numC 10) (numC 7))
                empty (numV -1) (numV -1))
        (numV 70))

  (test (interp-posn (newC 'posn (list (numC 2) (numC 7))))
        (objV 'posn (list (numV 2) (numV 7))))

  (test (interp-posn (sendC posn27 'mdist (numC 0)))
        (numV 9))
  
  (test (interp-posn (sendC posn27 'addX (numC 10)))
        (numV 12))

  (test (interp-posn (sendC (ssendC posn27 'posn 'factory12 (numC 0))
                            'multY
                            (numC 15)))
        (numV 30))

  (test (interp-posn (sendC posn531 'addDist posn27))
        (numV 18))
  
  (test/exn (interp-posn (plusC (numC 1) posn27))
            "not a number")
  (test/exn (interp-posn (getC (numC 1) 'x))
            "not found")
  (test/exn (interp-posn (sendC (numC 1) 'mdist (numC 0)))
            "not found")
  (test/exn (interp-posn (ssendC (numC 1) 'posn 'mdist (numC 0)))
            "not found")
  (test/exn (interp-posn (newC 'posn (list (numC 0))))
            "wrong field count")
  (test (interp (selectC (numC 0) (newC 'selclass empty))
                (list select-test-class)
                (numV -1)
                (numV -1))
        (numV 0))
  (test (interp (selectC (numC 1) (newC 'selclass empty))
                (list select-test-class)
                (numV -1)
                (numV -1))
        (numV 3))
  (test/exn (interp (selectC (newC 'object empty) (newC 'selclass empty))
                    (list select-test-class)
                    (numV -1)
                    (numV -1))
            "not a number")
  (test/exn (interp (selectC (numC 0) (numC 3))
                    (list select-test-class)
                    (numV -1)
                    (numV -1))
            "not found")
  (test/exn (interp-posn (selectC (numC 0) posn27))
            "not found")
  (test (interp-posn (instanceofC (newC 'object empty) 'object))
        (numV 0))
  (test (interp-posn (instanceofC posn531 'posn))
        (numV 0))
  (test (interp-posn (instanceofC posn27 'posn3D))
        (numV 1))
  (test (interp-posn (instanceofC (numC 3) 'object))
        (numV 0))
  (test (interp-posn (instanceofC (numC 3) 'posn))
        (numV 1))
  (test (interp (sendC (numC 1) 'select (newC 'selclass empty))
                (list select-test-class)
                (numV -1)
                (numV -1))
        (numV 3))
  (test (interp (sendC (numC 0) 'select (newC 'selclass empty))
                (list select-test-class)
                (numV -1)
                (numV -1))
        (numV 0))
  (test (interp (sendC (numC 1) 'plus (numC 2))
                empty
                (numV -1)
                (numV -1))
        (numV 3))
  (test/exn (interp-posn (sendC (numC 1) 'plus posn27))
            "not found")
  (test (interp (sendC (numC 1) 'mult (numC 2))
                empty
                (numV -1)
                (numV -1))
        (numV 2))
  (test/exn (interp-posn (sendC (numC 1) 'mult posn27))
            "not found"))

;; ============================================================
;; inherit

(define-type ExprI
  [numI (n : number)]
  [plusI (lhs : ExprI)
         (rhs : ExprI)]
  [multI (lhs : ExprI)
         (rhs : ExprI)]
  [argI]
  [thisI]
  [newI (class-name : symbol)
        (args : (listof ExprI))]
  [getI (obj-expr : ExprI)
        (field-name : symbol)]
  [sendI (obj-expr : ExprI)
         (method-name : symbol)
         (arg-expr : ExprI)]
  [superI (method-name : symbol)
          (arg-expr : ExprI)]
  [selectI (num : ExprI)
           (obj-expr : ExprI)]
  [instanceofI (obj-expr : ExprI)
               (ancestor-name : symbol)])

(define-type ClassI
  [classI (name : symbol)
          (super-name : symbol)
          (field-names : (listof symbol))
          (methods : (listof MethodI))])

(define-type MethodI
  [methodI (name : symbol)
           (body-expr : ExprI)])

(module+ test
  (print-only-errors true))

;; ----------------------------------------

(define (expr-i->c [a : ExprI] [super-name : symbol]) : ExprC
  (local [(define (recur expr)
            (expr-i->c expr super-name))]
    (type-case ExprI a
      [numI (n) (numC n)]
      [plusI (l r) (plusC (recur l) (recur r))]
      [multI (l r) (multC (recur l) (recur r))]
      [argI () (argC)]
      [thisI () (thisC)]
      [newI (class-name field-exprs)
            (newC class-name (map recur field-exprs))]
      [getI (expr field-name)
            (getC (recur expr) field-name)]
      [sendI (expr method-name arg-expr)
             (sendC (recur expr)
                    method-name
                    (recur arg-expr))]
      [superI (method-name arg-expr)
              (ssendC (thisC)
                      super-name
                      method-name
                      (recur arg-expr))]
      [selectI (num obj-expr)
               (selectC (recur num) (recur obj-expr))]
      [instanceofI (obj-expr ancestor-name)
                   (instanceofC (recur obj-expr) ancestor-name)])))

(module+ test
  (test (expr-i->c (numI 10) 'object)
        (numC 10))
  (test (expr-i->c (plusI (numI 10) (numI 2)) 'object)
        (plusC (numC 10) (numC 2)))
  (test (expr-i->c (multI (numI 10) (numI 2)) 'object)
        (multC (numC 10) (numC 2)))
  (test (expr-i->c (argI) 'object)
        (argC))
  (test (expr-i->c (thisI) 'object)
        (thisC))
  (test (expr-i->c (newI 'object (list (numI 1))) 'object)
        (newC 'object (list (numC 1))))
  (test (expr-i->c (getI (numI 1) 'x) 'object)
        (getC (numC 1) 'x))
  (test (expr-i->c (sendI (numI 1) 'mdist (numI 2)) 'object)
        (sendC (numC 1) 'mdist (numC 2)))
  (test (expr-i->c (superI 'mdist (numI 2)) 'posn)
        (ssendC (thisC) 'posn 'mdist (numC 2)))
  (test (expr-i->c (selectI (numI 0) (newI 'object (list (numI 1)))) 'object)
        (selectC (numC 0) (newC 'object (list (numC 1)))))
  (test (expr-i->c (instanceofI (numI 0) 'object) 'object)
        (instanceofC (numC 0) 'object)))

;; ----------------------------------------

(define (method-i->c [m : MethodI] [super-name : symbol]) : MethodC
  (type-case MethodI m
    [methodI (name body-expr) 
             (methodC name 
                      (expr-i->c body-expr super-name))]))

(module+ test
  (define posn3d-mdist-i-method
    (methodI 'mdist
             (plusI (getI (thisI) 'z)
                    (superI 'mdist (argI)))))
  (define posn3d-mdist-c-method
    (methodC 'mdist
             (plusC (getC (thisC) 'z)
                    (ssendC (thisC) 'posn 'mdist (argC)))))

  (test (method-i->c posn3d-mdist-i-method 'posn)
        posn3d-mdist-c-method))

;; ----------------------------------------

(define (class-i->c-not-flat [c : ClassI]) : ClassC
  (type-case ClassI c
    [classI (name super-name field-names methods)
            (classC
             name
             super-name
             field-names
             (map (lambda (m) (method-i->c m super-name))
                  methods))]))

(module+ test
  (define posn3d-i-class 
    (classI 'posn3d
            'posn
            (list 'z)
            (list posn3d-mdist-i-method)))
  (define posn3d-c-class-not-flat
    (classC 'posn3d
            'posn
            (list 'z)
            (list posn3d-mdist-c-method)))
  
  (test (class-i->c-not-flat posn3d-i-class)
        posn3d-c-class-not-flat))

;; ----------------------------------------

(define (flatten-class [c : ClassC] 
                       [classes : (listof ClassC)] 
                       [i-classes : (listof ClassI)]) : ClassC
  (type-case ClassC c
    [classC (name s-name field-names methods)
            (type-case ClassC (flatten-super name classes i-classes)
              [classC (super-name s-s-name super-field-names super-methods)
                      (classC
                       name
                       super-name
                       (add-fields super-field-names field-names)
                       (add/replace-methods super-methods methods))])]))

(define (flatten-super [name : symbol]
                       [classes : (listof ClassC)] 
                       [i-classes : (listof ClassI)]) : ClassC
  (type-case ClassI (find-i-class name i-classes)
    [classI (name super-name field-names i-methods)
            (if (equal? super-name 'object)
                base-object
                (flatten-class (find-class super-name classes)
                               classes
                               i-classes))]))

(module+ test
  (define posn-i-class 
    (classI 'posn
            'object
            (list 'x 'y)
            (list (methodI 'mdist
                           (plusI (getI (thisI) 'x)
                                  (getI (thisI) 'y)))
                  (methodI 'addDist
                           (plusI (sendI (thisI) 'mdist (numI 0))
                                  (sendI (argI) 'mdist (numI 0)))))))
  (define addDist-c-method
    (methodC 'addDist
             (plusC (sendC (thisC) 'mdist (numC 0))
                    (sendC (argC) 'mdist (numC 0)))))
  (define posn-c-class-not-flat
    (classC 'posn
            'object
            (list 'x 'y)
            (list (methodC 'mdist
                           (plusC (getC (thisC) 'x)
                                  (getC (thisC) 'y)))
                  addDist-c-method)))
  (define posn3d-c-class
    (classC 'posn3d
            'posn
            (list 'x 'y 'z)
            (list posn3d-mdist-c-method
                  addDist-c-method)))

  (test (flatten-class posn3d-c-class-not-flat
                       (list posn-c-class-not-flat
                             posn3d-c-class-not-flat)
                       (list posn-i-class
                             posn3d-i-class))
        posn3d-c-class))

;; ----------------------------------------

(define add-fields append)

(define (add/replace-methods [methods : (listof MethodC)]
                             [new-methods : (listof MethodC)])
  : (listof MethodC)
  (cond
    [(empty? new-methods) methods]
    [else (add/replace-methods
           (add/replace-method methods (first new-methods))
           (rest new-methods))]))

(define (add/replace-method [methods : (listof MethodC)] 
                            [new-method : MethodC])
  : (listof MethodC)
  (cond
    [(empty? methods) (list new-method)]
    [else
     (if (equal? (methodC-name (first methods))
                 (methodC-name new-method))
         (cons new-method (rest methods))
         (cons (first methods) 
               (add/replace-method (rest methods)
                                   new-method)))]))

(module+ test
  (test (add-fields (list 'x 'y) (list 'z))
        (list 'x 'y 'z))

  (test (add/replace-methods empty empty)
        empty)
  (test (add/replace-methods empty (list (methodC 'm (numC 0))))
        (list (methodC 'm (numC 0))))
  (test (add/replace-methods (list (methodC 'm (numC 0))) empty)
        (list (methodC 'm (numC 0))))
  (test (add/replace-methods (list (methodC 'm (numC 0)))
                             (list (methodC 'm (numC 1))))
        (list (methodC 'm (numC 1))))
  (test (add/replace-methods (list (methodC 'm (numC 0))
                                   (methodC 'n (numC 2)))
                             (list (methodC 'm (numC 1))))
        (list (methodC 'm (numC 1))
              (methodC 'n (numC 2))))
  (test (add/replace-methods (list (methodC 'm (numC 0)))
                             (list (methodC 'm (numC 1))
                                   (methodC 'n (numC 2))))
        (list (methodC 'm (numC 1))
              (methodC 'n (numC 2))))

  (test (add/replace-method (list (methodC 'm (numC 0)))
                            (methodC 'm (numC 1)))
        (list (methodC 'm (numC 1))))
  (test (add/replace-method (list (methodC 'm (numC 0)))
                            (methodC 'n (numC 2)))
        (list (methodC 'm (numC 0))
              (methodC 'n (numC 2)))))

;; ----------------------------------------

(define find-i-class : (symbol (listof ClassI) -> ClassI)
  (make-find classI-name))

;; ----------------------------------------

(define (interp-i [i-a : ExprI] [i-classes : (listof ClassI)]) : Value
  (local [(define a (expr-i->c i-a 'object))
          (define classes-not-flat (map class-i->c-not-flat i-classes))
          (define classes
            (map (lambda (c)
                   (flatten-class c classes-not-flat i-classes))
                 classes-not-flat))]
    (interp a classes (numV -1) (numV -1))))

(module+ test
  (test (interp-i (numI 0) empty)
        (numV 0))

  (test (interp-i
         (sendI (newI 'posn3d (list (numI 5) (numI 3) (numI 1)))
                'addDist
                (newI 'posn (list (numI 2) (numI 7))))
         (list posn-i-class
               posn3d-i-class))
        (numV 18)))

;; ============================================================
;; parse & interp-prog

(module+ test
  (print-only-errors true))

;; ----------------------------------------

(define (parse-class [s : s-expression]) : ClassI
  (cond
   [(s-exp-match? `{class SYMBOL extends SYMBOL {ANY ...} ANY ...} s)
    (classI (s-exp->symbol (second (s-exp->list s)))
            (s-exp->symbol (fourth (s-exp->list s)))
            (map parse-field
                 (s-exp->list (fourth (rest (s-exp->list s)))))
            (map parse-method 
                 (rest (rest (rest (rest (rest (s-exp->list s))))))))]
   [else (error 'parse-class "invalid input")]))

(define (parse-field [s : s-expression]) : symbol
  (cond
   [(s-exp-match? `SYMBOL s)
    (s-exp->symbol s)]
   [else (error 'parse-field "invalid input")]))

(define (parse-method [s : s-expression]) : MethodI
  (cond
   [(s-exp-match? `{SYMBOL ANY} s)
    (methodI (s-exp->symbol (first (s-exp->list s)))
             (parse (second (s-exp->list s))))]
   [else (error 'parse-method "invalid input")]))

(define (parse [s : s-expression]) : ExprI
  (cond
   [(s-exp-match? `NUMBER s) (numI (s-exp->number s))]
   [(s-exp-match? `arg s) (argI)]
   [(s-exp-match? `this s) (thisI)]
   [(s-exp-match? '{+ ANY ANY} s)
    (sendI (parse (second (s-exp->list s)))
           'plus
           (parse (third (s-exp->list s))))]
    ;(plusI (parse (second (s-exp->list s)))
     ;      (parse (third (s-exp->list s))))]
   [(s-exp-match? '{* ANY ANY} s)
    (sendI (parse (second (s-exp->list s)))
           'mult
           (parse (third (s-exp->list s))))]
    ;(multI (parse (second (s-exp->list s)))
     ;      (parse (third (s-exp->list s))))]
   [(s-exp-match? '{new SYMBOL ANY ...} s)
    (newI (s-exp->symbol (second (s-exp->list s)))
          (map parse (rest (rest (s-exp->list s)))))]
   [(s-exp-match? '{get ANY SYMBOL} s)
    (getI (parse (second (s-exp->list s)))
          (s-exp->symbol (third (s-exp->list s))))]
   [(s-exp-match? '{send ANY SYMBOL ANY} s)
    (sendI (parse (second (s-exp->list s)))
           (s-exp->symbol (third (s-exp->list s)))
           (parse (fourth (s-exp->list s))))]
   [(s-exp-match? '{super SYMBOL ANY} s)
    (superI (s-exp->symbol (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
   [(s-exp-match? '{select ANY ANY} s)
    (sendI (parse (second (s-exp->list s)))
           'select
           (parse (third (s-exp->list s))))]
    ;(selectI (parse (second (s-exp->list s)))
     ;        (parse (third (s-exp->list s))))]
   [(s-exp-match? '{instanceof ANY SYMBOL} s)
    (instanceofI (parse (second (s-exp->list s)))
                 (s-exp->symbol (third (s-exp->list s))))]
   [else (error 'parse "invalid input")]))

(module+ test
  (test (parse '0)
        (numI 0))
  (test (parse `arg)
        (argI))
  (test (parse `this)
        (thisI))
  (test (parse '{+ 1 2})
        (sendI (numI 1) 'plus (numI 2)))
  (test (parse '{* 1 2})
        (sendI (numI 1) 'mult (numI 2)))
  (test (parse '{new posn 1 2})
        (newI 'posn (list (numI 1) (numI 2))))
  (test (parse '{get 1 x})
        (getI (numI 1) 'x))
  (test (parse '{send 1 m 2})
        (sendI (numI 1) 'm (numI 2)))
  (test (parse '{super m 1})
        (superI 'm (numI 1)))
  (test (parse '{select 1 2})
        (sendI (numI 1) 'select (numI 2)))
  (test (parse '{instanceof 1 object})
        (instanceofI (numI 1) 'object))
  (test/exn (parse `x)
            "invalid input")

  (test (parse-field `x)
        'x)
  (test/exn (parse-field '{x 1})
            "invalid input")

  (test (parse-method `{m this})
        (methodI 'm (thisI)))
  (test/exn (parse-method `{m 1 2})
            "invalid input")
  
  (test (parse-class '{class posn3D extends posn
                             {x y z}
                             {m1 arg}
                             {m2 this}})
        (classI 'posn3D 'posn
                (list 'x 'y 'z)
                (list (methodI 'm1 (argI))
                      (methodI 'm2 (thisI)))))
  (test/exn (parse-class '{class})
            "invalid input"))

;; ----------------------------------------

(define (interp-prog [classes : (listof s-expression)] [a : s-expression]) : s-expression
  (let ([v (interp-i (parse a)
                     (map parse-class classes))])
    (type-case Value v
      [numV (n) (number->s-exp n)]
      [objV (class-name field-vals) `object])))

(module+ test
  (test (interp-prog
         (list
          '{class empty extends object
                  {}})
         '{new empty})
        `object)

 (test (interp-prog 
        (list
         '{class posn extends object
                 {x y}
                 {mdist {+ {get this x} {get this y}}}
                 {addDist {+ {send arg mdist 0}
                             {send this mdist 0}}}}
         
         '{class posn3D extends posn
                 {z}
                 {mdist {+ {get this z} 
                           {super mdist arg}}}})
        
        '{send {new posn3D 5 3 1} addDist {new posn 2 7}})
       '18)
  (test (interp-prog (list)
                     '{new object})
        `object)
  (test (interp-prog (list '{class snowball extends object
                                   {size}
                                   {zero this}
                                   {nonzero {new snowball {+ 1 {get this size}}}}})
                     '{get {select 0 {new snowball 1}} size})
        '1)
  (test (interp-prog (list '{class snowball extends object
                                   {size}
                                   {zero this}
                                   {nonzero {new snowball {+ 1 {get this size}}}}})
                     '{get {select {+ 1 2} {new snowball 1}} size})
        '2)
  (test (interp-prog (list '{class fish extends object
                                   {size color}})
                     '{instanceof {new fish 1 2} fish})
        '0)
  
  (test (interp-prog (list '{class fish extends object
                                   {size color}})
                     '{instanceof {new fish 1 2} object})
        '0)
  (test (interp-prog (list '{class fish extends object
                                   {size color}}
                           '{class shark extends fish
                                   {teeth}})
                     '{instanceof {new shark 1 2 3} fish})
        '0)
  (test (interp-prog (list '{class fish extends object
                                   {size color}}
                           '{class shark extends fish
                                   {teeth}})
                     '{instanceof {new shark 1 2 3} object})
        '0)
  (test (interp-prog (list '{class fish extends object
                                   {size color}}
                           '{class shark extends fish
                                   {teeth}})
                     '{instanceof {new fish 1 2} shark})
        '1)
  (test (interp-prog (list '{class fish extends object
                                   {size color}}
                           '{class spider extends object
                                   {legs}})
                     '{instanceof {new spider 8} fish})
        '1)
  (test (interp-prog (list)
                     '{instanceof 8 object})
        '0)
  (test (interp-prog (list)
                     '{send 8 plus 9})
        '17)
  (test (interp-prog (list)
                     '{send 8 mult 9})
        '72)
  (test (interp-prog (list '{class snowball extends object
                                   {size}
                                   {zero this}
                                   {nonzero {new snowball {+ 1 {get this size}}}}})
                     '{get {send 8 select {new snowball 10}} size})
        '11)
  
  (test/exn (interp-prog (list)
                        '{new number 5})
           "not found")
  (test/exn (interp-prog (list)
                        '{new _internal-number-Please$Dont$Guess$My$Name 5})
           "not found")
  (test/exn (interp-prog (list)
                         '{send 8 plus {new object}})
            "not found") ;; because caller gets swapped
  (test/exn (interp-prog (list)
                         '{+ 8 {new object}})
            "not found") ;; because caller gets swapped
  (test/exn (interp-prog (list)
                         '{send {new object} plus 8})
            "not found")
  (test/exn (interp-prog (list)
                         '{+ {new object} 8})
            "not found")
  (test (interp-prog (list
                      '{class zero extends object
                              {}
                              {plus arg}
                              {mult this}
                              {select {send arg zero 0}}})
                     '{+ 7 {* 8 {new zero}}})
        '7)
  (test (interp-prog (list
                      '{class infinity extends object
                              {}
                              {plus this}
                              {mult this}
                              {select {send arg nonzero 0}}})
                     '{+ 7 {new infinity}})
        `object)
  (test (interp-prog (list
                      '{class infinity extends object
                              {}
                              {plus this}
                              {mult this}
                              {select {send arg nonzero 0}}}
                      '{class snowball extends object
                                   {size}
                                   {zero this}
                                   {nonzero {new snowball {+ 1 {get this size}}}}})
                     '{get {select {new infinity} {new snowball 3}} size})
        '4))