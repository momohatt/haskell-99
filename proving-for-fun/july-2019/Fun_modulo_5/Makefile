all: Submission.vo

Defs.vo: Defs.v
	coqc Defs.v

Submission.vo: Submission.v Defs.vo
	coqc Submission.v

clean:
	rm -f *.vo *.glob

.PHONY: all clean