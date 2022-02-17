#include <stdio.h>
#include <string.h>
#include <stdlib.h>

int min( int a, int b) { 
    if (a > b) return b;
    return a;
}
int main(){
    FILE *fp = fopen("formula", "w");
    FILE *input = fopen("input.txt", "r");
    FILE *output = fopen("output.txt", "w");
    
    int i, j, n, m, k;

    for(i = 1; i <= 9; i++){
        for(j = 1; j <= 9; j++){
            for(n=1; n <= 9; n++){
                fprintf(fp, "(declare-const p%d%d%d Bool)\n", i, j, n);
            }
        }
    }

    char value[10];
     //each pre-assigned cell contains the given number
    fprintf(fp, "; pre-assigned\n");
    fprintf(fp, "(assert (and ");
    int row=1, col=1;
    while(fscanf(input, "%s", value)!=EOF) {
        if (strcmp(value, "?")!=0)
            fprintf(fp, "p%d%d%d ", row, col, atoi(value));
        if (col==9) {
            row++;
            col=1;
            continue;
        }
        col++;
    }

    fprintf(fp,"))\n") ;

    //each cell is assigned with exactly one number
    fprintf(fp, "; Q1\n");
    fprintf(fp, "(assert (and \n");
    for(i=1; i<=9; i++){
        fprintf(fp, "(and ");
        for(j=1; j<=9; j++){
            fprintf(fp, "(and ");
            for(n=1; n<=8; n++){
                fprintf(fp, "(and ");
                for(m=n+1; m<=9; m++){
                    fprintf(fp, "(not (and p%d%d%d p%d%d%d))", i, j, n, i, j, m);
                }
                fprintf(fp,")") ;
            }
            fprintf(fp,")") ;
        }
        fprintf(fp,")") ;
    }
    
    for(i=1; i<=9; i++){
        fprintf(fp, "(and ");
        for(j=1; j<=9; j++){
            fprintf(fp, "(or ");
            for(n=1; n<=9; n++){
                fprintf(fp, "p%d%d%d ", i, j, n);
            }
            fprintf(fp,")") ;
        }
        fprintf(fp,")") ;
    }
    fprintf(fp,"))\n") ;

    //each row has every number between 1 and 9
    fprintf(fp, "; Q2\n");
    fprintf(fp, "(assert (and ");
    for(i=1; i<=9; i++){
        fprintf(fp, "(and ");
        for(n=1; n<=9; n++){
            fprintf(fp, "(or ");
            for(j=1; j<=9; j++){
                fprintf(fp, "p%d%d%d ", i, j, n);
            }
            fprintf(fp,")") ;
        }
        fprintf(fp,")") ;
    }
    fprintf(fp,"))\n") ;

    //each column has every number between 1 and 9
    fprintf(fp, "; Q3\n");
    fprintf(fp, "(assert (and ");
    for(j=1; j<=9; j++){
        fprintf(fp, "(and ");
        for(n=1; n<=9; n++){
            fprintf(fp, "(or ");
            for(i=1; i<=9; i++){
                fprintf(fp, "p%d%d%d ", i, j, n);
            }
            fprintf(fp,")") ;
        }
        fprintf(fp,")") ;
    }
    fprintf(fp,"))\n") ;

    //each subgid has every number between 1 and 9
    fprintf(fp, "; Q4\n");
    fprintf(fp, "(assert (and ");
    for(int r=0; r<=2; r++){
        fprintf(fp, "(and ");
        for(int s=0; s <=2; s++){
            fprintf(fp, "(and ");
            for(n=1; n<=9; n++){
                fprintf(fp, "(or ");
                for(i=1; i<=3; i++){
                    fprintf(fp, "(or ");
                    for(j=1; j<=3; j++){
                        fprintf(fp, "p%d%d%d ", 3*r+i, 3*s+j, n);
                    }
                    fprintf(fp,")") ;
                }
                fprintf(fp,")") ;
            }
            fprintf(fp,")") ;
        }
        fprintf(fp,")") ;
    }
    fprintf(fp,"))\n") ;

    fprintf(fp,"; Q5\n") ;
	fprintf(fp,"(assert ") ;
	fprintf(fp,"(and ") ;
	for (i = 2 ; i <= 9 ; i++) {
		fprintf(fp,"(and ") ;
		for (j = 1 ; j <= 8 ; j++) {
            fprintf(fp, "(and ");
            for (n=1; n<=9; n++) {
                fprintf(fp,"(or (not p%d%d%d) (not p%d%d%d))\n", i, j, n, i - 1, 1 + j, n) ;
                //fprintf(fp,"(not (and p%d%d%d p%d%d%d))\n", i, j, n, i - 1, 1 + j, n) ;
            }
            fprintf(fp, ")");
		}
		fprintf(fp,") ") ;
	}
	fprintf(fp,"))\n") ;

    fprintf(fp,"; Q6\n") ;
	fprintf(fp,"(assert ") ;
	fprintf(fp,"(and ") ;
	for (i = 1 ; i <= 8 ; i++) {
		fprintf(fp,"(and ") ;
		for (j = 1 ; j <= 8 ; j++) {
            fprintf(fp,"(and ") ;
            for (n=1; n<=9; n++) {
                fprintf(fp,"(not (and p%d%d%d p%d%d%d))\n", i, j, n, i + 1, j + 1, n) ;
            }
            fprintf(fp, ")");
		}
		fprintf(fp,") ") ;
	}
	fprintf(fp,"))\n") ;

    fprintf(fp, "(check-sat)\n(get-model)\n");

    fclose(fp);

    
    FILE * fin = popen("z3 formula", "r") ;
	char buf[128];
    char bu[128];
    char tmp[128];
    int result[9][9] = {0};
	fscanf(fin, "%s %s", bu, buf);
    if (strcmp(bu, "unsat") == 0) {
        printf("No solution");
        fprintf(output, "No solution");
        pclose(fin);
        fclose(output);
        return 0;
    }
	while (!feof(fin)) {
		fscanf(fin, "%s", buf) ; //printf("%s ", buf) ;
		fscanf(fin, "%s", tmp) ; //printf("%s ", tmp) ;
		fscanf(fin, "%s", buf) ; //printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; //printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; //printf("%s\n", buf) ;
        if (strncmp(buf, "true", 4)==0) {
            int three_digit = atoi(&tmp[1]);
            int row = three_digit/100;
            int temp = three_digit%100;
            int column = temp/10;
            int num = temp%10;
            //printf("%d %d %d %d\n", three_digit, row, column, num);
            result[row-1][column-1] = num;
        }
	}

    for (int i=0; i<9; i++) {
        for (int j=0; j<9; j++) {
            printf("%d ", result[i][j]);
            fprintf(output, "%d ", result[i][j]);
        }
        if (i==8)
            break;
        printf("\n");
        fprintf(output, "\n");
    }
	pclose(fin) ;
    fclose(output);
}
