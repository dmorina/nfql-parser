.PHONY: all test clean bootstrap

clean:
	rm parser.out
	rm parsetab.py
	rm output/*
	
bootstrap: _virtualenv setup
	_virtualenv/bin/pip3-2 install -e .
ifneq ($(wildcard requirements.txt),)
	_virtualenv/bin/pip3-2 install -r test-requirements.txt
endif
	make clean

_virtualenv:
	virtualenv _virtualenv

test:
	mkdir -p output
	/usr/bin/env python3 src/main.py tests/query-https-tcp-session-parsed.flw > /dev/null
	/usr/bin/env python3 src/main.py tests/query-dns-udp-parsed.flw > /dev/null
	/usr/bin/env python3 src/main.py tests/query-http-octets-parsed.flw > /dev/null
	/usr/bin/env python3 src/main.py tests/query-http-tcp-session-parsed.flw > /dev/null
	/usr/bin/env python3 src/main.py tests/query-mdns-udp-parsed.flw > /dev/null
	/usr/bin/env python3 src/main.py tests/query-tcp-session-parsed.flw > /dev/null
	/usr/bin/env python3 src/tests.py
	mv tests/*.json output


