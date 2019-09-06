(ns clodjen.llvm-wrap
  (:require [clodjen.utils :refer [extract-arg-meta]]))

(import '[org.bytedeco.javacpp Pointer PointerPointer BytePointer FunctionPointer])
(import '[org.bytedeco.llvm.LLVM LLVMModuleRef LLVMTypeRef LLVMValueRef
          LLVMExecutionEngineRef LLVMGenericValueRef LLVMBasicBlockRef])
(import '[org.bytedeco.llvm.global LLVM])
(import '[com.sun.jna Function])
(require '[clojure.inspector :as insp])

(require '[clojure.pprint :as pp])

(defn initialize-jit []
  (LLVM/LLVMLinkInMCJIT)
  (LLVM/LLVMInitializeNativeAsmPrinter)
  (LLVM/LLVMInitializeNativeAsmParser)
  (LLVM/LLVMInitializeNativeTarget))

(initialize-jit)

(defn create-module [name]
  (LLVM/LLVMModuleCreateWithName name))

;; define integer types
(def types* (let [int-sizes [1 8 16 32 64 128]
                 int-type* #(symbol (str "LLVM/LLVMInt" % "Type"))
                 defs      (map (fn [x] [(keyword (str "i" x)) (eval `(~(int-type* x)))]) int-sizes)]
              (into {} defs)))

(defn throwing-map [initial-map]
  (fn [name]
    (if-let [t (types* name)]
      t
      (throw (Exception. (str "Unknown type " name))))))

(def types (throwing-map [types*]))

(def llvm-types (-> types* clojure.set/map-invert throwing-map))

(def c-types {:i1   Boolean
              :i8  Byte
              :i16 Short
              :i32 Integer
              :i64  Long })

(into {} (for [x [1 2 3]]
           [x (* 2 x)]))

(defn type-from-meta [sym]
  (if-let [sym-meta (meta sym)]
    (let [matched-types (filter sym-meta (keys types*))]
      (case (count matched-types)
        0 (throw (Exception. (str "No type was supplied for the block argument " sym)))
        1 nil
        (throw (Exception. (str "Multiple types supplied for the block argument " sym))))
      `(types ~(first matched-types)))
    (throw (Exception. (str "No type was supplied for the block argument " sym)))))

(defn declare-function
  [module fn-name ret-type args]
  `(let [arg-types# ~(vec (map type-from-meta args))
        arg-types-arr# (into-array LLVMTypeRef arg-types#)
        ret-type-llvm# (types ~ret-type)
        func#          (LLVM/LLVMAddFunction ~module ~fn-name (LLVM/LLVMFunctionType ret-type-llvm# (PointerPointer. arg-types-arr#) ~(count args) 0))]
    (LLVM/LLVMSetFunctionCallConv func# LLVM/LLVMCCallConv)
    {:func func# :args ~(vec (map name args)) :args-types arg-types# :ret ~ret-type :name ~fn-name :module ~module}))

(declare ^:dynamic builder)
(declare ^:dynamic blocks-map)
(declare ^:dynamic current-block)

(count (filter {:i1 true} (keys types*)))


(name :asdf)

(defn initialize-block [block]
  `(let [block-llvm# (LLVM/LLVMAppendBasicBlock ~'self ~(name (:name block)))]
    (LLVM/LLVMPositionBuilderAtEnd builder block-llvm#)
    (let [phis# ~(into {} (for [arg (:args block)]
                            `[~(keyword arg) (LLVM/LLVMBuildPhi builder ~(type-from-meta arg) ~(str arg))]))]
      {:name ~(:name block) :llvm block-llvm# :phis phis#})))

(defmacro define-function [module fn-name ret-type args bblocks]
  (let [block-to-map #(zipmap [:name :args :vars :term] %)
        blocks        (map block-to-map bblocks)
        func-info-sym (gensym)
        block-info-sym (gensym)]
    `(binding [builder (LLVM/LLVMCreateBuilder)]
       (let [~func-info-sym ~(declare-function module fn-name ret-type args)
             ~'self (:func ~func-info-sym)
             ~@(apply concat (map-indexed (fn [index arg] [arg `(get-param ~func-info-sym ~index)]) args))
             ~'blocks-map ~(into {}
                      (for [block blocks]
                        [(:name block) (initialize-block block)]))]
         (binding [blocks-map ~'blocks-map]
           ~@(for [block blocks]
              `(let [block-name#     ~(keyword (:name block))
                     ~block-info-sym (block-name# blocks-map)
                     block-llvm#     (:llvm ~block-info-sym)]
                 (binding [current-block ~block-info-sym]
                   (LLVM/LLVMPositionBuilderAtEnd builder block-llvm#)
                   (let
                       [~@(apply concat (for [arg-name (:args block)]
                                          [(symbol arg-name) `(~(keyword arg-name) (:phis ~block-info-sym))]))
                        ~@(apply concat (for [defs (partition 2 (:vars block))
                                              :let [[name form] defs]]
                                          [name (concat form [(str name)])]))]
                     ~(:term block))))))
         `(LLVM/LLVMDisposeBuilder builder)
         ~func-info-sym))))

(defn const [type value]
  (let [llvm-type (if (instance? LLVMTypeRef type) type (types type))]
    (LLVM/LLVMConstInt llvm-type value 1)))

(defn make-llvm-value [arg]
  (cond
    (instance? LLVMValueRef arg)           arg
    (and (seqable? arg) (= 2 (count arg))) (apply const arg)
    :default                               (throw (Exception. (str "Value arg " arg " should be either LLVMValueRef or a (type const) tuple")))))


(defn bind-phis [block args]
  (doseq [[phi val] (map vector (vals (:phis (block blocks-map))) args)]
    (LLVM/LLVMAddIncoming phi (make-llvm-value val) (:llvm current-block) 1)))

(defn branch [target & args]
  (let [block-info (target blocks-map)]
    (bind-phis target args)
    (LLVM/LLVMBuildBr builder (:llvm block-info))))

(defn cond-branch [cond [block-1 & args-1] [block-2 & args-2]]
  (do
    (bind-phis block-1 args-1)
    (bind-phis block-2 args-2)
    (let [get-block-llvm #(:llvm (% blocks-map))]
      (LLVM/LLVMBuildCondBr builder cond (get-block-llvm block-1) (get-block-llvm block-2)))))


(defmacro resolve-local-symbol [sym]
  (if-let [binding ((symbol sym) &env)]
    (symbol sym)
    'nil))


(defmacro defllvm [fn-name args body]
  (let [patch-value-sym (gensym)]
    `(defn ~fn-name [~@args ~'op-name]
       (let [~@(apply concat (for [arg  args
                              :when (:value (meta arg))]
                          `[~arg (make-llvm-value ~arg)]))]
         ~body))))

(defn make-phi [type name]
  (LLVM/LLVMBuildPhi builder type name))

(defn phi-incoming
  [phi values blocks]
  {:pre (= (count values) (count blocks))}
  (let [values-arr (into-array LLVMValueRef values)
        block-arr (into-array LLVMBasicBlockRef blocks)]
    (LLVM/LLVMAddIncoming phi (PointerPointer. values-arr) (PointerPointer. block-arr) (count values))))

(defllvm call-func [func args]
  (let [args-arr (into-array LLVMValueRef args)]
    (LLVM/LLVMBuildCall builder func (PointerPointer. args-arr) (count args) op-name)))

(defllvm mul [^:value val1 ^:value val2]
    (LLVM/LLVMBuildMul builder val1 val2 op-name))

(defllvm add [^:value val1 ^:value val2]
  (LLVM/LLVMBuildAdd builder val1 val2 op-name))

(defllvm sub [^:value val1 ^:value val2]
  (LLVM/LLVMBuildSub builder val1 val2 op-name))

(defllvm cmp
  [^:value val1 ^:value val2 op]
  (let [llvm-op (case op
                  :eq LLVM/LLVMIntEQ
                  :lt LLVM/LLVMIntSLT
                  :le LLVM/LLVMIntSLE
                  :ge LLVM/LLVMIntSGE
                  :gt LLVM/LLVMIntSGT)]
    (LLVM/LLVMBuildICmp builder llvm-op val1 val2 op-name)))

(defn int-cast
  ([value type] (int-cast value type ""))
  ([value type comment] (LLVM/LLVMBuildIntCast builder value type comment)))

(defn ret [val]
  (let [llvm-val (make-llvm-value val)]
    (LLVM/LLVMBuildRet builder val)))

(defn get-param [func idx] (LLVM/LLVMGetParam (:func func) idx))

(defn get-params [func] (into [] (map #(get-param func %) (range (count (:args func))))))

(defn optimize-module [mod]
  (let [pass (LLVM/LLVMCreatePassManager)]
    (LLVM/LLVMAddConstantMergePass pass)
    (LLVM/LLVMAddInstructionCombiningPass pass)
    (LLVM/LLVMAddPromoteMemoryToRegisterPass pass)
    (LLVM/LLVMAddGVNPass pass)
    (LLVM/LLVMAddCFGSimplificationPass pass)
    (LLVM/LLVMRunPassManager pass mod)
    (LLVM/LLVMDisposePassManager pass)
    mod))

(declare print-module)

(defn verify-module [mod]
  (let [error (BytePointer. (cast Pointer nil))]
    (LLVM/LLVMVerifyModule mod LLVM/LLVMPrintMessageAction error)
    (let [error-str (.getString error)]
      (LLVM/LLVMDisposeMessage error)
      (if (not (empty? error-str))
        (throw (Exception. (str "Module verify failed with: " error-str ", in module " (print-module mod))))))))

(defn print-module [mod]
  (let [buf (LLVM/LLVMPrintModuleToString mod)
        s (.getString buf)]
    (LLVM/LLVMDisposeMessage buf)
    s))

(defn make-execution-engine
  ([mod] (make-execution-engine mod true))
  ([mod verify]
   (do
     (when verify (verify-module mod))
     (let [engine     (LLVMExecutionEngineRef.)
           error      (BytePointer. (cast Pointer nil))
           mod-result (LLVM/LLVMCreateJITCompilerForModule engine mod 2 error)]
       (if (not= mod-result 0)
         (do
           (println (.getString error))
           (LLVM/LLVMDisposeMessage error)
           (System/exit -1))
         engine)))))

(defn dispose-execution-engine [engine]
  (LLVM/LLVMDisposeExecutionEngine engine))

(defn run-function
  [engine func & args]
  {:pre (= (count args) (count (:args func)))}
  (let [{func-llvm :func
         arg-types :args
         ret-type  :ret
         func-name :name
         func-mod :module} func
        func-addr (LLVM/LLVMGetFunctionAddress engine func-name)
        native-func (com.sun.jna.Function/getFunction (com.sun.jna.Pointer. func-addr) 0 "utf8")
        exec-args        (into-array args)
        exec-res         (.invoke native-func (c-types ret-type) exec-args)]
    exec-res))



(def mod (create-module "mod"))
(def fac
  (define-function mod "fac" :i64 [^:i64 x]
    [[:entry
      []
      [break (cmp x [:i64 1] :lt)]
      (cond-branch break [:ret [:i64 1]] [:cont x])]
     [:cont
      [^:i64 y]
      [y-next (sub y [:i64 1])
       res-next (call-func self [y-next])
       res-mul  (mul res-next y)]
      (branch :ret res-mul)]
     [:ret [^:i64 res] [] (ret res)]]))

(println (print-module mod))

(verify-module mod)

(def engine (make-execution-engine mod))

(run-function engine fac 10)

;; (def func (define-function mod "func" :i32 [^:i32 x]
;;             [
;;              [:entry [] [over21 (cmp x [:i32 21] :gt)] (cond-branch over21 [:then] [:else])]
;;              [:then [] [] (branch :done [:i32 1])]
;;              [:else [] [] (branch :done [:i32 0])]
;;              [:done [^:i32 res] [sum (add res [:i32 1])] (ret sum)]]))



;; (println (print-module mod))

;; (verify-module mod)

;;

;; (run-function engine func 22)
