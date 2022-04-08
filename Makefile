# Makefile for COMS W4112 Project 2, Spring 2022
# Written by Ken Ross

db4112: db4112.c
	gcc -O3 -mavx512f -o db4112 db4112.c
