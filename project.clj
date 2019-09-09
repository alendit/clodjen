(defproject clodjen "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "EPL-2.0 OR GPL-2.0-or-later WITH Classpath-exception-2.0"
            :url "https://www.eclipse.org/legal/epl-2.0/"}
  :dependencies [[org.clojure/clojure "1.10.0"]
                 [org.bytedeco/llvm-platform "8.0.0-1.5.1"]
                 [net.java.dev.jna/jna "5.4.0"]
                 [fn-fx/fn-fx-openjfx11 "0.5.0-SNAPSHOT"]
                 [orchestra "2019.02.06-1"]]
  :main ^:skip-aot clodjen.core
  :target-path "target/%s"
  :profiles {:uberjar {:aot :all}})
