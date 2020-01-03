#lang racket

;; You can require more modules of your choice.
(require racket/list
         (prefix-in utils: "utils.rkt")
         (prefix-in stats: "statistics.rkt"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                     ;;
;; Strategies                                                                          ;;
;; ==========                                                                          ;;
;; For the purpose of this assignment, just the `etai` strategy is expected, since     ;;
;; we have dictionary-closure and secret-word-enumeration to leap-frog to the right    ;;
;; key. This technique would fail for harder keys which are arbitrary permutations of  ;;
;; the alphabet. We will be forced to explore many more strategies (along with         ;;
;; dictionary-closure of course).                                                      ;;
;;                                                                                     ;;
;; Strategies to guess substitutions for the key using statistical information about   ;;
;; - the English language from utils.rkt                                               ;;
;; - the cipher text      from statistics.rkt                                          ;;
;;                                                                                     ;;
;; Follow the function signature as indicated below. Deviations will make it           ;;
;; impossible for automatic grading of your submission.                                ;;
;; Moreover, we do not expect your strategies to require any more/different            ;;
;; arguments. Note that you recieve the key as argument, so you can at the very        ;;
;; least ensure that all the substitutions are monoalphabetic wrt this key.            ;;
;;                                                                                     ;;
;; Signature:                                                                          ;;
;; ```                                                                                 ;;
;; (define (my-fundoo-strategy key)                                                    ;;
;;   ;; Make use of `utils:ciphertext`, `utils:cipher-word-list`                       ;;
;;   ...)                                                                              ;;
;; ```                                                                                 ;;
;;                                                                                     ;;
;; Substitutions                                                                       ;;
;; -------------                                                                       ;;
;; In order to extend the key incrementally, we use `utils:add-substitution` to        ;;
;; extend a given key with a substitution.                                             ;;
;;                                                                                     ;;
;; A substitution is a list of pairs, each pair mapping a plaintext char to a          ;;
;; ciphertext char. For example, to extend the key with T -> a and O -> r              ;;
;; (simultaneously), we use the substitution:                                          ;;
;; ```                                                                                 ;;
;; (list (cons #\T #\a) (cons #\O #\r))                                                ;;
;; ```                                                                                 ;;
;; For a single substitution use a singleton list (containing just one pair).          ;;
;;                                                                                     ;;
;; **CAUTION**                                                                         ;;
;; -----------                                                                         ;;
;; 1. Note that add-substitution does not do sanity checks on the substitution and use ;;
;;    of `utils:is-monoalphabetic` is recommended to ensure that you don't             ;;
;;    inadvertently create invalid keys.                                               ;;
;; 2. You must provide a list called `compositions` in this module.                    ;;
;;                                                                                     ;;
;; See docs in "utils.rkt" for more information.                                       ;;
;;                                                                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; You must add "public" functions of this module to this list.
(provide etai
         emptykey
         common
         slice
         remove-duplicates
         ;; Some more suggested strategies:
         
         ;; common-words-double
         ;; bigrams
         ;; common-initial-letters
         ;; common-final-letters
         ;; common-words-triple
         ;; trigrams
         ;; common-double-letters
         ;; common-words-quadruple
         ;; quadgrams
         
         ;; lists of strategies
         composition)

;; A strategy that uses some statistical information to generate potential
;; substitutions for E, T, A and I.
;; Refer the assignment manual for tips on developing this strategy. You can
;; interact with our etai with the executable we provide.
(define (slice l i j)
  (if (= j 0)
      '()
      (if (= i 1) (cons (car l) (slice (cdr l) 1 (- j 1)))
          (slice (cdr l) (- i 1) (- j 1)))))
(define (top-4 lst)
  (slice lst 1 4))

(define (removee l e) (foldr (lambda (x y) (if (eq? e x) y (cons x y))) '() l))
(define (remove-duplicates l) (foldr (lambda (x y) (if (null? y) (list x)
                                                       (cons x (removee y x)))) '() l))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (common l1 l2)
  (cond
    [(or (null? l1) (null? l2)) '()]
    [(index-of l2 (car l1)) (append (common (cdr l1) (remove (car l1) l2)) (list (car l1)))]
    [else (common (cdr l1) l2)]))

;stats:cipher-common-final-letters utils:cipher-word-list
;(define findfinals
;  (let ([intersection (common (top-4 (stats:cipher-common-final-letters utils:cipher-word-list)) non-single)])
;  (cond
;    [(= 2 (length intersection)) intersection]
;    [else #f])))

(define (sort-by-final-letter lst);to order giving preference to T in theai
  (let ([freq-list (stats:cipher-common-final-letters utils:cipher-word-list)])
    (sort lst (lambda (x y)
                (if(or (equal? #f (index-of freq-list (cdr (car x)))) (equal? #f (index-of freq-list (cdr (car y)))))
                   #t
               (< (index-of freq-list (cdr (car x))) (index-of freq-list (cdr (car y)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;ALL TYPES OF LISTS TAKEN FROM STATISTICS 
(define singles-strings (stats:cipher-common-words-single (utils:cipher-word-list-f utils:ciphertext)));single word strings
(define (fill ans singles monograms);takes top 4 of non-single monograms
  (cond
    [(= (length ans) 4) ans]
    [(not (index-of singles (car monograms))) (fill (append ans (list (car monograms))) singles (cdr monograms))]
    [else (fill ans singles (cdr monograms))]))
(define (singles-list-h strings-left)
  (cond
    [(null? strings-left) '()]
    [else (append (singles-list-h (cdr strings-left)) (list (stats:car-str (car strings-left))))]))
(define singles-list
  (singles-list-h singles-strings))
(define non-single (fill '() singles-list (stats:cipher-monograms utils:ciphertext)))
(define the-list (stats:cipher-trigrams (utils:cipher-word-list-f utils:ciphertext)))
(define first (car the-list))
(define second (cadr the-list))
(define third (caddr the-list))
(define fourth (car (cdddr the-list)))

;CENTRAL FUNCTIONS
(define (etai key)
  (let([al (car non-single)]
       [be (cadr non-single)]
       [ga (caddr non-single)]
       [ex (car singles-list)]
       [yi (cadr singles-list)])
    (sort-by-final-letter
     (list(list (cons #\E al) (cons #\T be) (cons #\A ex) (cons #\I yi))
          (list (cons #\E al) (cons #\T be) (cons #\A yi) (cons #\I ex))
             (list (cons #\E al) (cons #\T ga) (cons #\A ex) (cons #\I yi))
             (list (cons #\E al) (cons #\T ga) (cons #\A yi) (cons #\I ex))
             
             (list (cons #\E be) (cons #\T al) (cons #\A ex) (cons #\I yi))
             (list (cons #\E be) (cons #\T al) (cons #\A yi) (cons #\I ex))
             (list (cons #\E be) (cons #\T ga) (cons #\A ex) (cons #\I yi))
             (list (cons #\E be) (cons #\T ga) (cons #\A yi) (cons #\I ex))
             
             (list (cons #\E ga) (cons #\T al) (cons #\A ex) (cons #\I yi))
             (list (cons #\E ga) (cons #\T al) (cons #\A yi) (cons #\I ex))
             (list (cons #\E ga) (cons #\T be) (cons #\A ex) (cons #\I yi))
             (list (cons #\E ga) (cons #\T be) (cons #\A yi) (cons #\I ex))))))

(define (theai key)
  (sort-by-final-letter
   (cond
    [(null? (cdr singles-list))
     (append*
      (map (lambda(x) (if(utils:is-monoalphabetic? x emptykey)
                         (list x)
                         '()))
           (list(list (cons #\T (stats:car-str first))
                      (cons #\H (stats:car-str (stats:cdr-str first)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str first))))
                 (cons #\A (car singles-list)))
                (list (cons #\T (stats:car-str first))
                      (cons #\H (stats:car-str (stats:cdr-str first)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str first))))
                 (cons #\I (car singles-list)))
                (list (cons #\T (stats:car-str second))
                      (cons #\H (stats:car-str (stats:cdr-str second)))
                      (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str second))))
                      (cons #\A (car singles-list)))
           (list (cons #\T (stats:car-str second))
                 (cons #\H (stats:car-str (stats:cdr-str second)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str second))))
                 (cons #\I (car singles-list)))
           (list (cons #\T (stats:car-str third))
                 (cons #\H (stats:car-str (stats:cdr-str third)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str third))))
                 (cons #\A (car singles-list)))
           (list (cons #\T (stats:car-str third))
                 (cons #\H (stats:car-str (stats:cdr-str third)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str third))))
                 (cons #\I (car singles-list)))
           (list (cons #\T (stats:car-str fourth))
                 (cons #\H (stats:car-str (stats:cdr-str fourth)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str fourth))))
                 (cons #\A (car singles-list)))
           (list (cons #\T (stats:car-str fourth))
                 (cons #\H (stats:car-str (stats:cdr-str fourth)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str fourth))))
                 (cons #\I (car singles-list)))
           )))]
    [else
     (append*
      (map (lambda(x) (if(utils:is-monoalphabetic? x emptykey)
                         (list x)
                         '()))
           (list (list (cons #\T (stats:car-str first))
                 (cons #\H (stats:car-str (stats:cdr-str first)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str first))))
                 (cons #\A (car singles-list))
                 (cons #\I (cadr singles-list)))
           (list (cons #\T (stats:car-str first))
                 (cons #\H (stats:car-str (stats:cdr-str first)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str first))))
                 (cons #\A (cadr singles-list))
                 (cons #\I (car singles-list)))
           (list (cons #\T (stats:car-str second))
                 (cons #\H (stats:car-str (stats:cdr-str second)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str second))))
                 (cons #\A (car singles-list))
                 (cons #\I (cadr singles-list)))
           (list (cons #\T (stats:car-str second))
                 (cons #\H (stats:car-str (stats:cdr-str second)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str second))))
                 (cons #\A (cadr singles-list))
                 (cons #\I (car singles-list)))
           (list (cons #\T (stats:car-str third))
                 (cons #\H (stats:car-str (stats:cdr-str third)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str third))))
                 (cons #\A (car singles-list))
                 (cons #\I (cadr singles-list)))
           (list (cons #\T (stats:car-str third))
                 (cons #\H (stats:car-str (stats:cdr-str third)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str third))))
                 (cons #\A (cadr singles-list))
                 (cons #\I (car singles-list)))
           (list (cons #\T (stats:car-str fourth))
                 (cons #\H (stats:car-str (stats:cdr-str fourth)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str fourth))))
                 (cons #\A (car singles-list))
                 (cons #\I (cadr singles-list)))
           (list (cons #\T (stats:car-str fourth))
                 (cons #\H (stats:car-str (stats:cdr-str fourth)))
                 (cons #\E (stats:car-str (stats:cdr-str (stats:cdr-str fourth))))
                 (cons #\A (cadr singles-list))
                 (cons #\I (car singles-list)))
           )))]
    )))
(define (thai key)
  (define top-bigram (string->list (car (stats:cipher-bigrams (utils:cipher-word-list-f utils:ciphertext)))))
  (define next-bigram (string->list (cadr (stats:cipher-bigrams (utils:cipher-word-list-f utils:ciphertext)))))
  (let([ex (car singles-list)]
       [yi (cadr singles-list)])
  (list
   (list (cons #\T (car top-bigram)) (cons #\H (cadr top-bigram)) (cons #\A ex) (cons #\I yi))
   (list (cons #\T (car top-bigram)) (cons #\H (cadr top-bigram)) (cons #\A yi) (cons #\I ex))
   (list (cons #\T (car next-bigram)) (cons #\H (cadr next-bigram)) (cons #\A ex) (cons #\I yi))
   (list (cons #\T (car next-bigram)) (cons #\H (cadr next-bigram)) (cons #\A yi) (cons #\I ex)))))
;; A suggested composition of strategies that might work well. Has not been
;; exhaustively tested by us. Be original ;)
(define composition
  (if(null? (cdr singles-list))
     (list theai)
     (list theai etai thai)))
                  ;; common-words-double
;; bigrams
;; common-initial-letters
;; common-final-letters
;; common-words-triple
;; trigrams
;; common-double-letters))
;; common-words-quadruple
;; quadgrams))
(define emptykey (build-list 26 (lambda (x) #\_)))