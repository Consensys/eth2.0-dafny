#!/bin/bash

# use the docker container to run dafny

# compile and run tests in the test dir
docker run -v /Users/franck/development/eth2.0-dafny:/dafny -it dafny-2.3.0.10506 /bin/bash -c  'cd dafny' ; python3 scripts/runTests.py "test"
