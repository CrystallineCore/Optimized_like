# Makefile for optimized_like PostgreSQL extension

MODULE_big = optimized_like
OBJS = optimized_like.o
EXTENSION = optimized_like
DATA = optimized_like--1.1.sql

PGFILEDESC = "Optimized LIKE pattern matching with bitmap indexing"

# PostgreSQL module makefile
PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)

# Compiler flags for strict checking
override CFLAGS += -Wall -Wmissing-prototypes -Wpointer-arith -Werror=vla -Wendif-labels

# Build SQL script from template if needed
optimized_like--1.1.sql: optimized_like.sql
	cp $< $@

.PHONY: clean
clean:
	rm -f optimized_like.o optimized_like.so optimized_like--1.1.sql

install: optimized_like.so optimized_like--1.1.sql
	$(INSTALL) -d $(DESTDIR)$(pkglibdir)
	$(INSTALL) -m 755 optimized_like.so $(DESTDIR)$(pkglibdir)/
	$(INSTALL) -d $(DESTDIR)$(datadir)/extension
	$(INSTALL) -m 644 optimized_like.control $(DESTDIR)$(datadir)/extension/
	$(INSTALL) -m 644 optimized_like--1.1.sql $(DESTDIR)$(datadir)/extension/
