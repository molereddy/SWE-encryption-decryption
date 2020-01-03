#lang racket

;; You can require more modules of your choice.
(require racket/string
         racket/list
         (prefix-in utils: "utils.rkt"))

(provide secret-word-enumeration
         in-dict?
         matchlist
         atoz
         unique?)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                           ;;
;; Secret Word Enumeration                                                                   ;;
;; =======================                                                                   ;;
;;                                                                                           ;;
;; This step exploits the fact that all keys begin with a secret word that is a              ;;
;; proper SIX-LETTER word from the English dictionary.                                       ;;
;;                                                                                           ;;
;; Given a partial key, we can query the dictionary for a list of 6 letter words             ;;
;; that can potentially begin the key.                                                       ;;
;; We can then filter out potential candidates whose keys do not agree with our partial key. ;;
;;                                                                                           ;;
;; It is possible that given a (wrong) partial key, we discover that none of these           ;;
;; potential candidates can agree with our partial key. This really implies a                ;;
;; mistake in the choice of substitution, since dictionary-closure is completely             ;;
;; deterministic (modulo any bugs in your implementation :)                                  ;;
;;                                                                                           ;;
;; Hence, this function must return either of:                                               ;;
;; a. `#f` if there are no consistent candidates for this key.                               ;;
;; b. the original key if there are multiple consistent candidates.                          ;;
;; c. the complete key if there's only one consistent candidate!                             ;;
;;                                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (in-dict? word)
  (cond
    [(not (index-of utils:dictionary (string-upcase (list->string word)))) #f]
    [else #t]))

(define (fill-dict lst);DIFFERENT FROM dict-fill;gives #f if no word;list of possible words ;the one which is actually used; lst is the key
  (filldict lst utils:dictionary '()))
(define (filldict key dict ans)
  (cond
    [(and (null? dict) (null? ans)) #f]
    [(null? dict) ans]
    [(matchlist key (string->list (string-downcase (car dict))))
     (filldict key (cdr dict) (cons (string->list (string-downcase (car dict))) ans))]
    [else (filldict key (cdr dict) ans)]))

(define (next-alphabet char)
  (list-ref atoz (modulo (+ 1 (index-of atoz char)) 26)))
(define (next-key-alphabet char key);finds next alphabet for a particular  taking into account the key
  (cond
    [(index-of key (next-alphabet char)) (next-key-alphabet (next-alphabet char) key)]
    [else (next-alphabet char)]))

(define (matchlist l1 l2)
  (cond
    [(not (= (length l1) (length l2))) #f]
    [(null? l1) #t]
    [(or (equal? (car l1) #\_) (equal? (car l2) #\_)) (matchlist (cdr l1) (cdr l2))]
    [(equal? (car l1) (car l2)) (matchlist (cdr l1) (cdr l2))]
    [else #f]))
;;
(define atoz (build-list 26 (lambda(x) (integer->char (+ x 97)))))
;;
(define (keyin l) (append (list (car l)) (list (cadr l)) (list (caddr l)) (list(cadddr l)) (list (car(cddddr l))) (list(car(cdr(cddddr l))))))
;^^takes 1st 6
(define (keyfilled list index);checks whether key word is filled
  (cond
    [(= index 6) #t]
    [(equal? (list-ref list index) #\_) #f]
    [else (keyfilled list (+ 1 index))]))
;;;;

(define (slice l i j) (cond
                        [(> i j) '()]
                        [else (if (= j 0)
                                  '()
                                  (if (= i 1)
                                      (cons (car l) (slice (cdr l) 1 (- j 1)))
                                      (slice (cdr l) (- i 1) (- j 1))))]))

(define (dict-fill to-do full-list);gives full key given partial key (key word);l is the key, call with to-do = full-list IS NOT SAME AS fill-dicts
  (cond
    [(null? (cdr to-do)) full-list]
    [(char-alphabetic? (cadr to-do)) (dict-fill (cdr to-do) full-list)]
    [else (dict-fill
           (cdr to-do)
           (append
            (slice full-list 1 (- 27 (length to-do)))
            (list (next-key-alphabet (car to-do) full-list))
            (slice full-list (- 29 (length to-do)) 26)))]))

(define (take-is-unique lst)
  (filter unique? lst))
(define (unique? lst)
  (cond
    [(null? lst) #t]
    [(not (index-of (cdr lst) (car lst))) (unique? (cdr lst))]
    [else #f]))

;CENTRAL FUNCTIONS
(define (secret-word-enumeration key-after-dictionary-closure);; Returns a key or false (#f)
  (define (take-satisfies-rest lst)
    (filter satisfies-rest? lst))
  (define (satisfies-rest? k)
    (matchlist k  key-after-dictionary-closure))
  (let ([first6ofinput (keyin key-after-dictionary-closure)])
    (cond
      [(keyfilled first6ofinput 0)
     (if(in-dict? first6ofinput)
        (if(matchlist  key-after-dictionary-closure (utils:encryption-key (list->string first6ofinput)))
           (utils:encryption-key (list->string first6ofinput))    
              #f)
        #f)]
      [else
       (let ([cleaned-set-of-keys (take-satisfies-rest (take-is-unique (map (lambda (x) (utils:encryption-key (list->string x))) (fill-dict first6ofinput))))])
         (cond
           [(null? cleaned-set-of-keys) #f]
           [(null? (cdr cleaned-set-of-keys))
            (append* cleaned-set-of-keys)]
            [else key-after-dictionary-closure]))])))