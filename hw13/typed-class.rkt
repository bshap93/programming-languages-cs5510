#lang plai-typed

(require "class.rkt"
         "inherit.rkt")

(define-type ClassT
  [classT (name : symbol)
          (super-name : symbol)
          (fields : (listof FieldT))
          (methods : (listof MethodT))])

(define-type FieldT
  [fieldT (name : symbol)
          (type : Type)])

(define-type MethodT
  [methodT (name : symbol)
           (arg-type : Type)
           (result-type : Type)
           (body-expr : ExprI)])

(define-type Type
  [numT]
  [objT (class-name : symbol)]
  [arrT (el-type : Type)]
  [unsetT]
  [nullT]) ; necessary distinction from unsetT -- this and arg must be prohibited in main expression

(module+ test
  (print-only-errors true))

;; ----------------------------------------

(define find-classT
  (make-find classT-name))

(define find-fieldT
  (make-find fieldT-name))

(define find-methodT
  (make-find methodT-name))

(define (type-error a msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string a)
                      (string-append " not "
                                     msg)))))

(define (get-all-field-types class-name t-classes)
  (if (equal? class-name 'object)
      empty        
      (type-case ClassT (find-classT class-name t-classes)
        [classT (name super-name fields methods)
                (append 
                 (get-all-field-types super-name t-classes)
                 (map fieldT-type fields))])))

;; ----------------------------------------

(define (make-find-in-tree find-in-list extract)
  (lambda (name t-class t-classes)
    (local [(define items (extract t-class))
            (define super-name 
              (classT-super-name t-class))]
      (if (equal? super-name 'object)
          (find-in-list name items)
          (try (find-in-list name items)
               (lambda ()
                 ((make-find-in-tree find-in-list extract)
                  name 
                  (find-classT super-name t-classes)
                  t-classes)))))))

(define find-field-in-tree
  (make-find-in-tree find-fieldT classT-fields))

(define find-method-in-tree
  (make-find-in-tree find-methodT classT-methods))

;; ----------------------------------------

(define (is-subclass? name1 name2 t-classes)
  (cond
    [(equal? name1 name2) true]
    [(equal? name1 'object) false]
    [else
     (type-case ClassT (find-classT name1 t-classes)
       [classT (name super-name fields methods)
               (is-subclass? super-name name2 t-classes)])]))

(define (is-subtype? t1 t2 t-classes)
  (type-case Type t1
    [objT (name1)
          (type-case Type t2 
            [objT (name2)
                  (is-subclass? name1 name2 t-classes)]
            [else false])] ; no object is a subtype of null
    [nullT () (or (objT? t2) (equal? t1 t2))] ; null is a subtype of every object, and itself
    [else (equal? t1 t2)]))

(module+ test
  (define a-t-class (classT 'a 'object empty empty))
  (define b-t-class (classT 'b 'a empty empty))

  (test (is-subclass? 'object 'object empty)
        true)
  (test (is-subclass? 'a 'b (list a-t-class b-t-class))
        false)
  (test (is-subclass? 'b 'a (list a-t-class b-t-class))
        true)

  (test (is-subtype? (numT) (numT) empty)
        true)
  (test (is-subtype? (numT) (objT 'object) empty)
        false)
  (test (is-subtype? (objT 'object) (numT) empty)
        false)
  (test (is-subtype? (objT 'a) (objT 'b) (list a-t-class b-t-class))
        false)
  (test (is-subtype? (objT 'b) (objT 'a) (list a-t-class b-t-class))
        true)
  (test (is-subtype? (nullT) (objT 'a) (list a-t-class))
        true)
  (test (is-subtype? (nullT) (nullT) empty)
        true)
  (test (is-subtype? (objT 'a) (nullT) (list a-t-class))
        false))

;; ----------------------------------------

(define typecheck-expr : (ExprI (listof ClassT) Type Type -> Type)
  (lambda (expr t-classes arg-type this-type)
    (local [(define (recur expr)
              (typecheck-expr expr t-classes arg-type this-type))
            (define (typecheck-nums l r)
              (type-case Type (recur l)
                [numT ()
                      (type-case Type (recur r)
                        [numT () (numT)]
                        [else (type-error r "num")])]
                [else (type-error l "num")]))
            (define (array-op array index func)
              (type-case Type (recur index)
                [numT () (type-case Type (recur array)
                           [arrT (el-type) (func el-type)]
                           [else (type-error array "array")])]
                [else (type-error index "num")]))]
      (type-case ExprI expr
        [numI (n) (numT)]
        [plusI (l r) (typecheck-nums l r)]
        [multI (l r) (typecheck-nums l r)]
        [argI () (type-case Type arg-type ; main expression `this` and `arg` are not allowed
                   [unsetT () (error 'typecheck "arg not bound")]
                   [else arg-type])]
        [thisI () (type-case Type this-type
                    [unsetT () (error 'typecheck "this not bound")]
                    [else this-type])]
        [newI (class-name)
              (begin
                (get-all-field-types class-name t-classes) ; implicitly validates the class-name
                (objT class-name))]
        [getI (obj-expr field-name)
              (get-obj-field-type obj-expr (recur obj-expr) field-name t-classes)]
        [setI (obj-expr field-name arg-expr)
              (local [(define obj-type (recur obj-expr))]
                (if (is-subtype? (recur arg-expr) (get-obj-field-type obj-expr obj-type field-name t-classes) t-classes)
                    obj-type
                    (type-error expr "field type mismatch")))]
        [sendI (obj-expr method-name arg-expr)
               (local [(define obj-type (recur obj-expr))
                       (define arg-type (recur arg-expr))]
                 (type-case Type obj-type
                   [objT (class-name)
                         (typecheck-send class-name method-name
                                         arg-expr arg-type
                                         t-classes)]
                   [else
                    (type-error obj-expr "object")]))]
        [superI (method-name arg-expr)
                (local [(define arg-type (recur arg-expr))
                        (define this-class (type-case Type this-type
                                             [objT (class-name) (find-classT class-name t-classes)]
                                             [else (error 'typecheck "this not bound")]))]
                  (typecheck-send (classT-super-name this-class)
                                  method-name
                                  arg-expr arg-type
                                  t-classes))]
        [castI (type-name arg-expr)
               (local [(define arg-type (recur arg-expr))
                       (define sym-type (objT type-name))]
                 (if (or (is-subtype? arg-type sym-type t-classes)
                         (is-subtype? sym-type arg-type t-classes))
                     sym-type
                     (error 'typecheck "impossible cast")))]
        [if0I (tst thn els)
              (type-case Type (recur tst)
                [numT () (least-upper-bound (recur thn) (recur els) t-classes)]
                [else (type-error tst "num")])]
        [nullI () (nullT)]
        [newarrayI (type-name size init-expr)
                   (type-case Type (recur size)
                     [numT () (local [(define init-type (recur init-expr))
                                      (define el-type (objT type-name))]
                                (if (is-subtype? init-type el-type t-classes)
                                    (arrT el-type)
                                    (type-error init-type (to-string el-type))))]
                     [else (type-error size "num")])]
        [arrayrefI (array index)
                   (array-op array index
                             (lambda (el-type) el-type))]
        [arraysetI (array index arg-expr)
                   (array-op array index
                             (lambda (el-type) (if (is-subtype? (recur arg-expr) el-type t-classes)
                                                   (numT)
                                                   (type-error arg-expr (to-string el-type)))))]))))

(define (get-obj-field-type obj-expr t-obj field-name t-classes)
  (type-case Type t-obj
    [objT (class-name)
          (local [(define t-class
                    (find-classT class-name t-classes))
                  (define field
                    (find-field-in-tree field-name
                                        t-class
                                        t-classes))]
            (type-case FieldT field
              [fieldT (name type) type]))]
    [else (type-error obj-expr "object")]))

(define (least-upper-bound type-a type-b t-classes)
  (type-case Type type-a
    [objT (a-class-name)
          (type-case Type type-b
            [objT (b-class-name)
                  (least-common-superclass a-class-name b-class-name t-classes)]
            [nullT () type-a]
            [else (type-error type-a (to-string type-b))])]
    [nullT () (if (or (objT? type-b) (equal? type-a type-b)) ; null is upper-bounded by any object, or null
                  type-b
                  (type-error type-a (to-string type-b)))]
    [else (if (equal? type-a type-b)
              type-a
              (type-error type-a (to-string type-b)))]))

(define (least-common-superclass name-a name-b t-classes) ; not terribly efficient right now but gets the job done
  (if (is-subclass? name-a name-b t-classes)
      (objT name-b)
      (type-case ClassT (find-classT name-b t-classes)
        [classT (name super-name fields methods)
                (least-common-superclass name-a super-name t-classes)])))

(define (typecheck-send [class-name : symbol]
                        [method-name : symbol]
                        [arg-expr : ExprI]
                        [arg-type : Type]
                        [t-classes : (listof ClassT)])
  (type-case MethodT (find-method-in-tree
                      method-name
                      (find-classT class-name t-classes)
                      t-classes)
    [methodT (name arg-type-m result-type body-expr)
             (if (is-subtype? arg-type arg-type-m t-classes)
                 result-type
                 (type-error arg-expr (to-string arg-type-m)))]))

(define (typecheck-method [method : MethodT]
                          [this-type : Type]
                          [t-classes : (listof ClassT)]) : ()
  (type-case MethodT method
    [methodT (name arg-type result-type body-expr)
             (if (is-subtype? (typecheck-expr body-expr t-classes
                                              arg-type this-type)
                              result-type
                              t-classes)
                 (values)
                 (type-error body-expr (to-string result-type)))]))

(define (check-override [method : MethodT]
                        [this-class : ClassT]
                        [t-classes : (listof ClassT)])
  (local [(define super-name 
            (classT-super-name this-class))
          (define super-method
            (try
             ;; Look for method in superclass:
             (find-method-in-tree (methodT-name method)
                                  (find-classT super-name t-classes)
                                  t-classes)
             ;; no such method in superclass:
             (lambda () method)))]
    (if (and (equal? (methodT-arg-type method)
                     (methodT-arg-type super-method))
             (equal? (methodT-result-type method)
                     (methodT-result-type super-method)))
        (values)
        (error 'typecheck (string-append
                           "bad override of "
                           (to-string (methodT-name method)))))))

(define (typecheck-class [t-class : ClassT] [t-classes : (listof ClassT)])
  (type-case ClassT t-class
    [classT (name super-name fields methods)
            (map (lambda (m)
                   (begin
                     (typecheck-method m (objT name) t-classes)
                     (check-override m t-class t-classes)))
                 methods)]))

(define (typecheck [a : ExprI] [t-classes : (listof ClassT)]) : Type
  (begin
    (map (lambda (t-class)
           (typecheck-class t-class t-classes))
         t-classes)
    (typecheck-expr a t-classes (unsetT) (unsetT))))

;; ----------------------------------------

(module+ test
  (define posn-t-class
    (classT 'posn 'object
            (list (fieldT 'x (numT)) (fieldT 'y (numT)))
            (list (methodT 'mdist (numT) (numT) 
                           (plusI (getI (thisI) 'x) (getI (thisI) 'y)))
                  (methodT 'addDist (objT 'posn) (numT)
                           (plusI (sendI (thisI) 'mdist (numI 0))
                                  (sendI (argI) 'mdist (numI 0)))))))

  (define posn3D-t-class 
    (classT 'posn3D 'posn
            (list (fieldT 'z (numT)))
            (list (methodT 'mdist (numT) (numT)
                           (plusI (getI (thisI) 'z) 
                                  (superI 'mdist (argI)))))))

  (define posn3D2-t-class 
    (classT 'posn3D2 'posn
            (list (fieldT 'w (numT)))
            (list (methodT 'mdist (numT) (numT)
                           (plusI (getI (thisI) 'w) 
                                  (superI 'mdist (argI)))))))

  (define square-t-class 
    (classT 'square 'object
            (list (fieldT 'topleft (objT 'posn))
                  (fieldT 'other (objT 'posn3D)))
            (list (methodT 'dup (objT 'posn) (objT 'square)
                           (setI (setI (newI 'square) 'topleft (getI (thisI) 'topleft)) 'other (nullI))))))

  (define (typecheck-posn a)
    (typecheck a
               (list posn-t-class posn3D-t-class posn3D2-t-class square-t-class)))
  
  (define posn27 (setI (setI (newI 'posn) 'x (numI 2)) 'y (numI 7)))
  (define posn531 (setI (setI (setI (newI 'posn3D) 'x (numI 5)) 'y (numI 3)) 'z (numI 1)))
  (define posn135 (setI (setI (setI (newI 'posn3D2) 'x (numI 1)) 'y (numI 3)) 'w (numI 5)))
  (define square-posn27 (setI (setI (newI 'square) 'topleft posn27) 'other (nullI)))

  (define reflector-t-class
    (classT 'reflector 'object
            (list)
            (list (methodT 'arg (numT) (numT)
                           (argI))
                  (methodT 'this (numT) (objT 'reflector)
                           (thisI)))))

  (test (typecheck-posn (sendI posn27 'mdist (numI 0)))
        (numT))
  (test (typecheck-posn (sendI posn531 'mdist (numI 0)))
        (numT))  
  (test (typecheck-posn (sendI posn531 'addDist posn27))
        (numT))  
  (test (typecheck-posn (sendI posn27 'addDist posn531))
        (numT))

  (test (typecheck-posn (setI (newI 'square) 'topleft (setI (setI (newI 'posn) 'x (numI 0)) 'y (numI 1))))
        (objT 'square))
  (test (typecheck-posn (setI (setI (newI 'square) 'topleft (setI (setI (setI (newI 'posn3D) 'x (numI 0)) 'y (numI 1)) 'z (numI 3))) 'other (nullI)))
        (objT 'square))
  
  (test (typecheck (multI (numI 1) (numI 2))
                   empty)
        (numT))

  (test/exn (typecheck-posn (sendI (numI 10) 'mdist (numI 0)))
            "no type")
  (test/exn (typecheck-posn (sendI posn27 'mdist posn27))
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'object))
                       empty)
            "no type")
  (test/exn (typecheck (plusI (newI 'object) (numI 1))
                       empty)
            "no type")
  (test/exn (typecheck (plusI (numI 1) (setI (newI 'object) 'x (numI 1)))
                       empty)
            "not found")
  (test/exn (typecheck (getI (numI 1) 'x)
                       empty)
            "no type")
  (test/exn (typecheck (numI 10)
                       (list posn-t-class 
                             (classT 'other 'posn
                                     (list)
                                     (list (methodT 'mdist 
                                                    (objT 'object) (numT)
                                                    (numI 10))))))
            "bad override")
  (test/exn (typecheck-method (methodT 'm (numT) (objT 'object) (numI 0)) (objT 'object) empty)
            "no type")
  (test/exn (typecheck (numI 0)
                       (list square-t-class
                             (classT 'cube 'square
                                     empty
                                     (list
                                      (methodT 'm (numT) (numT)
                                               ;; No such method in superclass:
                                               (superI 'm (numI 0)))))))
            "not found")

  ; Test that the typechecker disallows use of unset `this` and `arg`
  (test (typecheck (sendI (newI 'reflector) 'arg (numI 22)) (list reflector-t-class))
        (numT))
  (test (typecheck (sendI (newI 'reflector) 'this (numI 0)) (list reflector-t-class))
        (objT 'reflector))
  (test/exn (typecheck (sendI (newI 'reflector) 'arg (argI)) (list reflector-t-class))
            "arg not bound")
  (test/exn (typecheck (thisI) (list))
            "this not bound")
  (test/exn (typecheck (argI) (list))
            "arg not bound")
  (test/exn (typecheck (superI 'method (numI 0)) (list))
            "this not bound")

  ; Test cast
  (test (typecheck-posn (castI 'object posn27))
        (objT 'object))
  (test (typecheck-posn (castI 'posn3D posn27))
        (objT 'posn3D))
  (test/exn (typecheck (castI 'num (numI 1)) (list))
            "impossible cast") ; built-in num is different then from a num class
  (test/exn (typecheck-posn (castI 'posn square-posn27))
            "impossible cast")
  (test/exn (typecheck (castI 'object (numI 1)) (list))
            "impossible cast")

  ; Test if0
  (test (typecheck (if0I (numI 0) (numI 1) (numI 2)) (list))
        (numT))
  (test (typecheck-posn (if0I (numI 0) posn27 posn27))
        (objT 'posn))
  (test (typecheck-posn (if0I (numI 0) posn531 posn27))
        (objT 'posn))
  (test (typecheck-posn (if0I (numI 0) posn27 square-posn27))
        (objT 'object))
  (test (typecheck-posn (if0I (numI 0) posn531 posn135))
        (objT 'posn))
  (test/exn (typecheck-posn (if0I posn27 (numI 1) (numI 2)))
            "no type")
  (test/exn (typecheck-posn (if0I (numI 0) posn27 (numI 1)))
            "no type")
  (test/exn (typecheck-posn (if0I (numI 0) (numI 1) posn27))
            "no type")

  ; Test null
  (test (typecheck-posn (if0I (numI 0) (nullI) posn27)) ; null + if0
        (objT 'posn))
  (test (typecheck-posn (if0I (numI 0) (nullI) (nullI)))
        (nullT))
  (test (typecheck-posn (if0I (numI 0) posn27 (nullI)))
        (objT 'posn))
  (test/exn (typecheck (if0I (numI 0) (nullI) (numI 1)) (list))
        "no type")
  
  (test/exn (typecheck-posn (getI (nullI) 'x)) ; null get and send
            "no type")
  (test/exn (typecheck-posn (sendI (nullI) 'm (numI 0)))
            "no type")

  (test (typecheck-posn (newI 'square)) ; unused null field value and arg value
        (objT 'square))
  (test (typecheck-posn (sendI (newI 'square) 'dup (nullI)))
        (objT 'square))

  ; Test set
  (test (typecheck-posn (setI (newI 'square) 'topleft posn531))
        (objT 'square))
  (test/exn (typecheck-posn (setI (newI 'square) 'other posn27))
            "field type mismatch")

  ; Test array operations
  (test (typecheck-posn (newarrayI 'posn (numI 5) posn531))
        (arrT (objT 'posn)))
  (test/exn (typecheck-posn (newarrayI 'posn posn27 posn27))
            "no type")
  (test/exn (typecheck-posn (newarrayI 'posn3D (numI 5) posn27))
            "no type")
  (test (typecheck-posn (arrayrefI (newarrayI 'posn (numI 5) posn27) (numI 2)))
        (objT 'posn))
  (test/exn (typecheck-posn (arrayrefI (newarrayI 'posn (numI 5) posn27) posn27))
            "no type")
  (test/exn (typecheck-posn (arrayrefI (numI 2) (numI 3)))
            "no type")
  (test (typecheck-posn (arraysetI (newarrayI 'posn3D (numI 0) posn531) (numI 0) posn531))
        (numT))
  (test/exn (typecheck-posn (arraysetI (newarrayI 'posn3D (numI 0) posn531) posn27 posn531))
            "no type")
  (test/exn (typecheck-posn (arraysetI (numI 0) (numI 0) posn27))
            "no type")
  (test/exn (typecheck-posn (arraysetI (newarrayI 'posn3D (numI 5) posn531) (numI 0) posn27))
            "no type"))

;; ----------------------------------------

(define strip-types : (ClassT -> ClassI)
  (lambda (t-class)
    (type-case ClassT t-class
      [classT (name super-name fields methods)
              (classI
               name 
               super-name
               (map fieldT->fieldC fields)
               (map (lambda (m)
                      (type-case MethodT m
                        [methodT (name arg-type result-type body-expr)
                                 (methodI name body-expr)]))
                    methods))])))

(define (fieldT->fieldC field)
  (type-case FieldT field
    [fieldT (name type)
            (type-case Type type
              [numT () (fieldC name (numBT))]
              [objT (class-name) (fieldC name (objBT))]
              [else (error 'strip-types "unknown basetype")])]))

(module+ test
  (test (fieldT->fieldC (fieldT 'z (numT)))
        (fieldC 'z (numBT)))
  (test (fieldT->fieldC (fieldT 'y (objT 'some-class)))
        (fieldC 'y (objBT)))
  (test/exn (fieldT->fieldC (fieldT 'x (unsetT)))
            "unknown basetype"))

(define interp-t : (ExprI (listof ClassT) -> Value)
  (lambda (a t-classes)
    (interp-i a
              (map strip-types t-classes))))

(module+ test
  (define (interp-t-posn a)
    (interp-t a
              (list posn-t-class posn3D-t-class)))
  
  (test (interp-t-posn (sendI posn27 'mdist (numI 0)))
        (numV 9))  
  (test (interp-t-posn (sendI posn531 'mdist (numI 0)))
        (numV 9))
  (test (interp-t-posn (sendI posn531 'addDist posn27))
        (numV 18))
  (test (interp-t-posn (sendI posn27 'addDist posn531))
        (numV 18)))
