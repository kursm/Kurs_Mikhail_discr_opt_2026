#!/bin/bash

g++ -O3 checker.cpp -lClp -lCoinUtils -o runbin
./runbin
rm runbin
