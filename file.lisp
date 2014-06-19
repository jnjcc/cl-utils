(defun read-file-content (fpath)
  "read the entire content of file FPATH into string"
  (with-open-file (fp fpath)
    (let ((content (make-string (file-length fp))))
      (read-sequence content fp)
      content)))
