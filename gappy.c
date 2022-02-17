#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(){
    FILE * fp = fopen("formula_gappy", "w");

    int i, j;

    for(i = 1; i < 10; i++){
        for(j = 1; j < 10; j++){
            fprintf(fp, "(declare-const p%d%dB Bool)\n", i, j);
            fprintf(fp, "(declare-const p%d%dW Bool)\n", i, j);
        }
    }
    FILE * input = fopen("input_gappy.txt", "r");
    int lable[2][9] = {0};

    //insert the input data to lable
    
    for(i=0; i<2; i++){
        for(j=0; j<9; j++){
            fscanf(input, "%d", &lable[i][j]);
            //lable[0][j] = row lable
            //lable[1][j] = column lable
        }
    }
    fclose(input);

    int row, col;
    
    //cell have only one color
    fprintf(fp, "; ONE COLOR\n");
    fprintf(fp, "(assert (and ");
        for(row=1; row<10; row++){
            fprintf(fp, "(and ");
            for(col=1; col<10; col++){
                fprintf(fp, "(or (and (not p%d%dW) p%d%dB) (and p%d%dW (not p%d%dB)))", row, col, row, col, row, col, row, col);
            }
            fprintf(fp, ")\n");
        }
        fprintf(fp, "))\n");

    //no two black cells are adjacent to each other
    fprintf(fp, "; NOT ADJACENT B IN ROW\n");  //↔
    fprintf(fp, "(assert (and ");
    for(row=1; row<10; row++){
        fprintf(fp, "(and ");
        for(col=1; col<9; col++){
            fprintf(fp, "(not (and p%d%dB p%d%dB))", row, col, row, col+1);   
            }
            fprintf(fp, ")");
        }fprintf(fp, "))\n");

    fprintf(fp, "; NOT ADJACENT B IN COL\n"); //⇕
    fprintf(fp, "(assert (and ");
    for(col=1; col<10; col++){
        fprintf(fp, "(and ");
        for(row=1; row<9; row++){
            fprintf(fp, "(not (and p%d%dB p%d%dB))", row, col, row+1, col);   
            }
            fprintf(fp, ")");
        }fprintf(fp, "))\n");

    fprintf(fp, "; NOT ADJACENT B IN RIGHT-DIAGONAL \n"); //⇘
    fprintf(fp, "(assert (and ");
    for(row=1; row<9; row++){
        fprintf(fp, "(and ");
        for(col=1; col<9; col++){
            fprintf(fp, "(not (and p%d%dB p%d%dB))", row, col, row+1, col+1);   
            }
            fprintf(fp, ")");
        }fprintf(fp, "))\n");

    fprintf(fp, "; NOT ADJACENT B IN LEFT-DIAGONAL\n"); //⇙
    fprintf(fp, "(assert (and ");
    for(row=1; row<9; row++){
        fprintf(fp, "(and ");
        for(col=2; col<10; col++){
            fprintf(fp, "(not (and p%d%dB p%d%dB))", row, col, row+1, col-1);   
            }
            fprintf(fp, ")");
        }fprintf(fp, "))\n");

fprintf(fp, "; ROW EXIST\n");
    int term, mid;
    fprintf(fp, "(assert (and ");
    for(row=1; row<10; row++){
        fprintf(fp, "(or ");
        term = lable[0][row-1];
        for(col=1; col < 9-term; col++){
            fprintf(fp, "(and p%d%dB", row, col);
            for(mid=1; mid<term+1; mid++){
                fprintf(fp, " p%d%dW", row, col+mid);
            }
            fprintf(fp, " p%d%dB)", row, col+term+1);
        }
        fprintf(fp, ")\n");
    }
    fprintf(fp, "))\n");

fprintf(fp, "; ROW UNIQUE\n");
    int c;
    fprintf(fp, "(assert (and ");
    for(row=1; row<10; row++){
        fprintf(fp, "(and ");
        term = lable[0][row-1];
        for(col=1; col < 9-term-1; col++){
            fprintf(fp, "(and ");
            for(c = col+1; c < 9-term; c++){
                fprintf(fp, "(not (and"); 
                fprintf(fp, "(and p%d%dB", row, col);
                    for(mid=1; mid<term+1; mid++){
                        fprintf(fp, " p%d%dW", row, col+mid);
                        }
                fprintf(fp, " p%d%dB)", row, col+term+1);
                fprintf(fp, "(and p%d%dB", row, c);
                    for(mid=1; mid<term+1; mid++){
                        fprintf(fp, " p%d%dW", row, c+mid);
                        }
                fprintf(fp, " p%d%dB)", row, c+term+1);
                fprintf(fp, "))");
            }
            fprintf(fp, ")\n");
        }
        fprintf(fp, ")\n");
    }
    fprintf(fp, "))\n");

fprintf(fp, "; COLUMN EXIST\n");
    fprintf(fp, "(assert (and ");
    for(col=1; col<10; col++){
        fprintf(fp, "(or ");
        term = lable[1][col-1];
        for(row=1; row < 9-term; row++){
            fprintf(fp, "(and p%d%dB", row, col);
            for(mid=1; mid<term+1; mid++){
                fprintf(fp, " p%d%dW", row+mid, col);
            }
            fprintf(fp, " p%d%dB)", row+term+1, col);
        }
        fprintf(fp, ")\n");
    }
    fprintf(fp, "))\n");

fprintf(fp, "; COLUMN UNIQUE\n");
    int r;
    fprintf(fp, "(assert (and ");
    for(col=1; col<10; col++){
        fprintf(fp, "(and ");
        term = lable[0][col-1];
        for(row=1; row < 9-term-1; row++){
            fprintf(fp, "(and ");
            for(r = row+1; r < 9-term; r++){
                fprintf(fp, "(not (and ");
                fprintf(fp, "(and p%d%dB", row, col);
                for(mid=1; mid<term+1; mid++){
                    fprintf(fp, " p%d%dW", row+mid, col);
                }
                fprintf(fp, " p%d%dB)", row+term+1, col);
                fprintf(fp, "(and p%d%dB", r, col);
                for(mid=1; mid<term+1; mid++){
                    fprintf(fp, " p%d%dW", r+mid, col);
                }
                fprintf(fp, " p%d%dB)", r+term+1, col);
                fprintf(fp, "))");
            }
            fprintf(fp, ")\n");
        }
        fprintf(fp, ")\n");
    }
    fprintf(fp, "))\n");

    fprintf(fp, "(check-sat)\n(get-model)\n");
    fclose(fp);

    //print the result
    FILE * z3 = popen("z3 formula_gappy", "r");
    FILE *output = fopen("output_gappy.txt", "w");
    char result [9][9];
    char buf[400];
    char bu[100];
    char tmp[128];
    char bol[128];
    fscanf(z3, "%s %s", bu, buf);
    if(strcmp(bu, "unsat")==0) {
        printf("No solution");
        fprintf(output, "No solution");
        pclose(z3);
        fclose(output);
        return 0;
    }
    while(!feof(z3) && z3!=NULL){
        fscanf(z3, "%s", buf) ; //printf("%s ", buf) ;
        fscanf(z3, "%s", tmp) ; //printf("%s ", tmp) ;
        fscanf(z3, "%s", buf) ; //printf("%s ", buf) ;
        fscanf(z3, "%s", buf) ; //printf("%s ", buf) ;
        fscanf(z3, "%s", bol) ; //printf("%s\n", buf) ;
        if(strncmp(bol, "true", 4)==0){
            char word = tmp[strlen(tmp)-1];
            int row = atoi(&tmp[1])/10-1;
            int col = atoi(&tmp[2])-1;
            //printf("(%d,%d,%c)",row, col, word);
            result[row][col] = word;
        }
        
    }
    printf("\n");

    for (int i=0; i<9; i++) {
        for (int j=0; j<9; j++) {
            if(result[i][j]=='W' || result[i][j]=='B'){
                printf("%c ", result[i][j]);
                fprintf(output, "%c ", result[i][j]);
            }
            else {
                printf("? ");
                fprintf(output, "? ");
            }
        }
        printf("\n");
        fprintf(output, "\n");
    }
	pclose(z3) ;
    fclose(output);

    return 0;
}