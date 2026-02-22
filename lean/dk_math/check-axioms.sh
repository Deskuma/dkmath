#!/bin/bash

./lean-build.sh -v | grep -A10 "info:" | grep -A4 "axioms"
