FRAMA-C = frama-c
FRAMA-C-GUI = frama-c-gui
FRAMA-C_OPTIONS = -cpp-command="gcc -C -E -I ./include -I ./src" -wp

proof:	src/my_string.c
	$(FRAMA-C) $(FRAMA-C_OPTIONS) $<

proof-gui:	src/my_string.c
	$(FRAMA-C-GUI) $(FRAMA-C_OPTIONS) $<
