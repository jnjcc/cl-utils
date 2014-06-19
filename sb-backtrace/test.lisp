;;;; Testcase for sb-backtrace.lisp
(load "sb-backtrace.lisp")
(declaim (optimize debug))
(defun foo (x)
  (let ((y (+ x 3)))
    (backtrace-with-extra-info)
    (+ x y)))
(foo 1024)
(fresh-line)
