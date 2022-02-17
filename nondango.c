#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main() {
    FILE * fp = fopen("formula", "w");
    for (int i=1 ; i <= 10; i++) {
        for (int j = 1 ; j <= 10 ; j++) {
            fprintf(fp,"(declare-const p%d%dB Bool)\n", i, j) ;
            fprintf(fp,"(declare-const p%d%dW Bool)\n", i, j) ;
            fprintf(fp,"(declare-const p%d%dX Bool)\n", i, j) ;
        }
    }
    int grid_info[10][10] = {0};

    //read input.txt and get information
    FILE * input = fopen("input.txt", "r");
    int row=0, column = 0, nums;
    char value[10];
    char word = 'W';

    fprintf(fp, "(assert (and ");
    while(fscanf(input, "%s", value)!=EOF) {
        //  there is 'W' in the string(value)
        if (value[strlen(value)-1] == 'W') {
            char temp[10]={0};
            char number[10] = {0};
            strcat(temp, &value[0]);
            for (int i=0; i<strlen(temp); i++) {
                number[i] = temp[i];
            }
            nums = atoi(number);
            grid_info[row][column] = nums;
            fprintf(fp, "(not p%d%dX) ", row+1, column+1);
        }
        //  there is only numbers in the string(value)
        else {
            grid_info[row][column] = atoi(value);
            fprintf(fp, "(and p%d%dX (not p%d%dB) (not p%d%dW)) ", row+1, column+1, row+1, column+1, row+1, column+1);
        }
        if (column==9) {
            row++;
            column=0;
            continue;
        }
        column++;
    }
    fprintf(fp, "))\n");
    fclose(input);

    //storing the grid information (there is N squares in # grid)
    int gridsize[32]={0};
    for(int n=1; n<33; n++) {
        for(int i=0; i<10; i++) {
            for(int j=0; j<10; j++) {
                if(grid_info[i][j] == n)
                    gridsize[n-1]++;
            }
        }
    }

    // there exists exactly one B in a grid
    fprintf(fp,"(assert (and ");
    for(int n=0; n<32; n++) {   
        int count=0;
        int grid_idxs[10] = {0};
        fprintf(fp,"(or ");
        // checking if grid_info[i][j] is in the same grid (한 grid 안에 있는 {row, column} 구하기)
        for(int i=0; i<10; i++) {
            for(int j=0; j<10; j++) {
                if(grid_info[i][j] == n+1) {
                    if (j==9)
                        grid_idxs[count] = (i+1)*100+(j+1);
                    else 
                        grid_idxs[count] = (i+1)*10+j+1;
                    count++;
                }
            }
        }
        // adding the uniqueness to a grid to have exactly one B in a grid using the stored grid_idxs
        for(int i=0; i<10; i++) {   
            if(grid_idxs[i] == 0)
                break;
            fprintf(fp,"(and ");
            fprintf(fp,"p%dB ", grid_idxs[i]);
            for (int j=0; j<10; j++) {
                if (i==j)
                    continue;
                else if (grid_idxs[j]==0)
                    break;
                else 
                    fprintf(fp, "(not p%dB) ", grid_idxs[j]);
            }
            fprintf(fp,")");
        }
        fprintf(fp,")");

    }
    fprintf(fp,"))\n");

    // every square is (B and not W and not X) or (W and not B and not X) or (X and not B and not W)
    fprintf(fp, "(assert (and ");
    for (int i=1; i<=10; i++) {
        for (int j=1; j<=10; j++) {
            fprintf(fp, "(or (and p%d%dB (not p%d%dW) (not p%d%dX)) (and p%d%dW (not p%d%dB) (not p%d%dX)) (and p%d%dX (not p%d%dB) (not p%d%dW)))", i, j, i, j, i, j, i, j, i, j, i, j, i, j, i, j, i, j);
        }
    }
    fprintf(fp, "))\n");

    int col, sum;
    //no three circles in row
    fprintf(fp, "; ROW\n");
    fprintf(fp, "(assert (and ");
        for(row=1; row<=10; row++){
            fprintf(fp, "(and ");
            for(col=2; col<=9; col++){
                fprintf(fp, "(not (and p%d%dW p%d%dW p%d%dW))", row, col-1, row, col, row, col+1);
            }
            fprintf(fp, ")");
        }
    //fprintf(fp, ") (and ");
        for(row=1; row<=10; row++){
            fprintf(fp, "(and ");
            for(col=2; col<=9; col++){
                fprintf(fp, "(not (and p%d%dB p%d%dB p%d%dB))", row, col-1, row, col, row, col+1);
            }
            fprintf(fp, ")");
        }
    fprintf(fp, "))\n");

    //no three circles in col
    fprintf(fp, "; COLUMN\n");
    fprintf(fp, "(assert (and ");
        for(col=1; col<=10; col++){
            fprintf(fp, "(and ");
            for(row=2; row<=9; row++){
                fprintf(fp, "(not (and p%d%dW p%d%dW p%d%dW))", row-1, col, row, col, row+1, col);
            }
            fprintf(fp, ")");
        }
    //fprintf(fp, ")");
    //fprintf(fp, "(and ");
        for(col=1; col<=10; col++){
            fprintf(fp, "(and ");
            for(row=2; row<=9; row++){
                fprintf(fp, "(not (and p%d%dB p%d%dB p%d%dB))", row-1, col, row, col, row+1, col);
            }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");
    
    // no three circles in diagonal
    fprintf(fp,"; DIAGNAL_1\n") ; 
	fprintf(fp,"(assert ") ;
	fprintf(fp,"(and ") ;
    fprintf(fp,"(and ") ;
	    for (row = 2 ; row <= 9 ; row++) {
		    fprintf(fp,"(and ") ;
		    for (col = 2 ; col <= 9 ; col++) {
                fprintf(fp,"(not (and p%d%dW p%d%dW p%d%dW))\n", row-1, col-1, row, col, row+1, col+1) ;
            }
            fprintf(fp,") ") ;
		}
		fprintf(fp,")\n ") ;
    fprintf(fp,"(and ") ;
	    for (row = 2 ; row <= 9 ; row++) {
		    fprintf(fp,"(and ") ;
		    for (col = 2 ; col <= 9 ; col++) {
                fprintf(fp,"(not (and p%d%dB p%d%dB p%d%dB))\n", row-1, col-1, row, col, row+1, col+1) ;
            }
            fprintf(fp,") ") ;
		}
		fprintf(fp,") ") ;
	fprintf(fp,"))\n") ;

    fprintf(fp,"; DIAGNAL_2\n") ; 
	fprintf(fp,"(assert ") ;
	fprintf(fp,"(and ") ;
    fprintf(fp,"(and ") ;
	    for (row = 2 ; row <= 9 ; row++) {
		    fprintf(fp,"(and ") ;
		    for (col = 2 ; col <= 9 ; col++) {
                fprintf(fp,"(not (and p%d%dW p%d%dW p%d%dW))\n", row+1, col-1, row, col, row-1, col+1) ;
            }
            fprintf(fp,") ") ;
		}
		fprintf(fp,")\n ") ;
    fprintf(fp,"(and ") ;
	    for (row = 2 ; row <= 9 ; row++) {
		    fprintf(fp,"(and ") ;
		    for (col = 2 ; col <= 9 ; col++) {
                fprintf(fp,"(not (and p%d%dB p%d%dB p%d%dB))\n", row+1, col-1, row, col, row-1, col+1) ;
            }
            fprintf(fp,") ") ;
		}
		fprintf(fp,") ") ;
	fprintf(fp,"))\n") ;

    fprintf(fp, "(check-sat)\n(get-model)\n");
    fclose(fp);

    // printing the result
    FILE * z3 = popen("z3 formula", "r");
    FILE *output = fopen("output.txt", "w");
    char result[10][10];
    char buf[400];
    char bu[100];
    char tmp[128];
    char num[5]={0};
    fscanf(z3, "%s %s", bu, buf);
    if (strcmp(bu, "unsat") == 0) {
        printf("No solution");
        fprintf(output, "No solution");
        pclose(z3);
        fclose(output);
        return 0;
    }
    while (!feof(z3) && z3!=NULL) {
        fscanf(z3, "%s", buf) ; //printf("%s ", buf) ;
        fscanf(z3, "%s", tmp) ; //printf("%s ", tmp) ;
        fscanf(z3, "%s", buf) ; //printf("%s ", buf) ;
        fscanf(z3, "%s", buf) ; //printf("%s ", buf) ;
        fscanf(z3, "%s", buf) ; //printf("%s\n", buf) ;
        if (strncmp(buf, "true", 4)==0) {
            char word = tmp[strlen(tmp)-1];
            char temp[10]={0};
            char number[10] = {0};
            strcat(temp, &tmp[1]);
            for (int i=0; i<strlen(temp)-1; i++) {
                number[i] = temp[i];
            }
            int num = atoi(number);
            if (num>1000) 
                row = col = 9;
            else if (num>100) {
                if (num%100 < 10) {
                    row = 9;
                    col = num-100-1;
                }
                else {
                    row = num/100-1;
                    col = 9;
                }
            }
            else {
                row = num/10-1;
                col = num%10-1;
            }

            result[row][col] = word;
        }
    }

    for (int i=0; i<10; i++) {
        for (int j=0; j<10; j++) {
            if (result[i][j] == 'W' || result[i][j] == 'B' || result[i][j] == 'X') {
                printf("%c ", result[i][j]);
                fprintf(output, "%c ", result[i][j]);
            }
            else {
                printf("? ");
                fprintf(output, "? ");
            }
        }
        if (i==9)
            break;
        printf("\n");
        fprintf(output, "\n");
    }
    pclose(z3);
    fclose(output);
    return 0;
}