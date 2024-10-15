#!/bin/zsh 
for i in $(seq 1 2); do
    stack run egraphGP -- -d nikuradse_2.csv -g 5000 -a BestFirst -s 10 >> best_results_50_5.txt
    echo "============================================\n" >> best_results_50_5.txt 
done
for i in $(seq 1 10); do
    stack run egraphGP -- -d nikuradse_2.csv -g 5000 -a OnlyRandom -s 10 >> random_results_50_5.txt
    echo "============================================\n" >> random_results_50_5.txt 
done
