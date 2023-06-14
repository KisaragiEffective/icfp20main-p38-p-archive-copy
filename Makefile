LEAN_BIN=$(LEAN_ROOT)/bin
LEAN=$(LEAN_BIN)/lean
LEANC=$(LEAN_BIN)/leanc
PROJECT_ROOT=.
SRCS = $(shell cd $(PROJECT_ROOT); find . -name '*.lean')
OUT ?= out
DEPS = $(addprefix $(OUT)/,$(SRCS:.lean=.depend))
OBJS = $(SRCS:.lean=.olean)
C_OBJS = $(addprefix $(OUT)/,$(SRCS:.lean=.o))
ESC_OUT=$(subst /,\\/,$(OUT))
CPPFLAGS = -I$(HOME)/lean/lean4/src -O3

.PHONY: all clean version dump_out

all: $(C_OBJS)

runTermExperiment: $(OUT)/RunTermExperiment.o $(OUT)/Paper.o
	$(LEANC) -o $@ $^

dump_out: $(SRCS:.lean=.out)

depends: $(DEPS)

$(OUT)/%.depend: %.lean
# use separate assignment to ensure failure propagation
	@mkdir -p $(OUT)
	@ deps=`$(LEAN) --deps $< | python relative.py`; echo $(<:.lean=.olean): $$deps > $@

%.out: %.lean $(addprefix $(OUT)/,%.depend)
	@ echo produce $@
	@ $(LEAN) $< > $@ 2>&1

%.ir: %.lean $(addprefix $(OUT)/,%.depend)
	@ echo produce $@
	@ $(LEAN) -D trace.compiler.ir.init=true $< > $@ 2>&1

%.olean: %.lean $(addprefix $(OUT)/,%.depend)
	@echo "[    ] Building $<"
	@mkdir -p $(OUT)/$(*D)
	@ $(LEAN) --make --c="$(OUT)/$*.c.tmp" $<
# create the .c file atomically
	mv "$(OUT)/$*.c.tmp" "$(OUT)/$*.c"
# make sure the .olean file is newer than the .depend file to prevent infinite make cycles
	@touch $@

$(OUT)/%.c: %.olean
	@

$(OUT)/%.o: $(OUT)/%.c
	@echo "[    ] Building $<"
	@mkdir -p "$(@D)"
	@ $(LEANC) -c -o $@ $< $(LEANC_OPTS) $(CPPFLAGS)

clean:
	rm -rf $(OUT) $(OBJS) $(C_OBJS)

version:
	$(LEAN) -v

.PRECIOUS: $(OUT)/%.depend $(OUT)/%.c

include $(DEPS)
