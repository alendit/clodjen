(ns clodjen.llvm-wrap-test
  (:require [clojure.string :as str]
            [clodjen.llvm-wrap :refer :all]
            [clojure.test :refer :all]))

(defn trim-module [mod]
  (-> mod print-module str/trim-newline))

(defmacro test-func [test-descr fn-name ret-type arg-types blocks expected-llvm test-cases]
  `(testing ~test-descr
    (let [module# (create-module (str ~fn-name "_module"))
          func-ref# (declare-function module# ~fn-name ~ret-type ~arg-types)]
      (define-function func-ref# ~blocks)
      (verify-module module#)
      (is (= ~expected-llvm (trim-module module#)))
      (let [engine# (make-execution-engine module#)
            ~'func (fn [& args#] (apply run-function engine# func-ref# args#))]
        ~@test-cases))))

(deftest simple-func
  (test-func "Define and execute a simple function"
             "fac" :i32 [:i32]
             [[:entry [] [eq (cmp (params 0) [:i32 1] :eq)
                         res (int-cast eq (types :i32))]
               (ret res)]]
             "; ModuleID = 'fac_module'
source_filename = \"fac_module\"

define i32 @fac(i32) {
entry:
  %eq = icmp eq i32 %0, 1
  %res = sext i1 %eq to i32
  ret i32 %res
}"
             [(is (= 0 (func 0)))
              (is (= -1 (func 1)))]))

(deftest add-func
  (test-func "Define and execute an adder func"
             "add" :i32 [:i32 :i32]
             [[:entry [] [p0 (params 0)
                          p1 (params 1)
                          sum     (add p0 p1)]
               (ret sum)]]
             "; ModuleID = 'add_module'
source_filename = \"add_module\"

define i32 @add(i32, i32) {
entry:
  %add = add i32 %0, %1
  ret i32 %add
}"
             [(is (= 12 (func 6 6)))
              (is (= 24 (func 21 3)))]))

(deftest branching-func
  (test-func "Define and execute a branching func"
             "over21" :i1 [:i32]
             [[:entry []
               [over (cmp (params 0) [:i32 21] :gt)]
               (cond-branch over [:then] [:else])]
              [:then [] [] (branch :done [:i1 1])]
              [:else [] [] (branch :done [:i1 0])]
              [:done [^:i1 res] [] (ret res)]]
             "; ModuleID = 'over21_module'
source_filename = \"over21_module\"

define i1 @over21(i32) {
entry:
  %over = icmp sgt i32 %0, 21
  br i1 %over, label %then, label %else

then:                                             ; preds = %entry
  br label %done

else:                                             ; preds = %entry
  br label %done

done:                                             ; preds = %else, %then
  %res = phi i1 [ true, %then ], [ false, %else ]
  ret i1 %res
}"
             [(is (= true (func 22)))
              (is (= false (func 20)))]))

;; (deftest branching-func-args
;;   (test-func "Define and execute a branching func with block args"
;;              "over21" :i1 [:i32]
;;              [[entry (let [over (cmp (params 0) [:i32 21] :gt)])]]))
