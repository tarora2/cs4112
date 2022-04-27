/*
  COMS W4112 Project 2, Spring 2022
  Written by Ken Ross
  Copyright (c) The Trustees of Columbia University in the City of New York

  See class project handout for more extensive documentation.
*/

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/time.h>
#include <asm/unistd.h>
#include <immintrin.h>

/* uncomment out the following line for debug info during run */
#define DEBUG
int64_t idx = 0;


/* compare two int64_t values - for use with qsort */
static int compare (const void *p1, const void *p2)
{
  int a, b;
  a = *(int64_t *)p1;
  b = *(int64_t *)p2;
  if (a < b) return -1;
  if (a == b) return 0;
  return 1;
}

/* initialize searches and data - data is sorted and searches is a random permutation of data */
int init (int64_t *data, int64_t *searches, int count)
{
  for (int64_t i = 0; i < count; i++)
	{
	  searches[i] = random ();
	  data[i] = searches[i] + 1;
	}
  qsort (data, count, sizeof (int64_t), compare);
}

/* initialize outer probes of band join */
int band_init (int64_t *outer, int64_t size)
{
  for (int64_t i = 0; i < size; i++)
	{
	  outer[i] = random ();
	}
}

inline int64_t simple_binary_search(int64_t * data, int64_t size, int64_t searchkey)
{
	int64_t left = 0;
	int64_t right = size;
	int64_t mid;

	while(left<=right) 
	{
		mid = (left + right) / 2;   /* ignore possibility of overflow of left+right */
		if (data[mid]==searchkey) 
			return mid;
		if (data[mid]<searchkey)
			left = mid + 1;
		else
			right = mid - 1;
	}
	return -1; /* no match */
}

inline int64_t lower_bound(int64_t * data, int64_t size, int64_t searchkey)
{
	/* this binary search variant
	(a) does only one comparison in the inner loop
	(b) doesn't require an exact match; instead it returns the index of the first key >= the search key.
		That's good in a DB context where we might be doing a range search, and using binary search to
	identify the first key in the range.
	(c) If the search key is bigger than all keys, it returns size.
	*/
	int64_t left = 0;
	int64_t right = size;
	int64_t mid;

	while(left<right) 
	{
		mid = (left + right) / 2;   /* ignore possibility of overflow of left+right */
		if (data[mid]>=searchkey)
			right = mid;
		else
			left = mid + 1;
	}
	return right;
}

inline int64_t lower_bound_nb_arithmetic(int64_t* data, int64_t size, int64_t searchkey)
{
  /* this binary search variant
     (a) does no comparisons in the inner loop by using multiplication and addition
to convert control dependencies
         to data dependencies
     (b) doesn't require an exact match; instead it returns the index of the first 
key >= the search key.
         That's good in a DB context where we might be doing a range search, and 
using binary search to
 identify the first key in the range.
     (c) If the search key is bigger than all keys, it returns size.
  */
  int64_t left=0;
  int64_t right=size;
  int64_t mid;
  
  while(left<right) {
    mid = (left + right)/2;   /* ignore possibility of overflow of left+right */
    int64_t test = (data[mid]>=searchkey);
    right=mid*test + right*(1-test);
    left=(mid+1)*(1-test) + left*test;
  }
  return right;
}

inline int64_t lower_bound_nb_mask(int64_t * data, int64_t size, int64_t searchkey)
{
	/* this binary search variant
	(a) does no comparisons in the inner loop by using bit masking operations to convert control dependencies
		to data dependencies
	(b) doesn't require an exact match; instead it returns the index of the first key >= the search key.
		That's good in a DB context where we might be doing a range search, and using binary search to
	identify the first key in the range.
	(c) If the search key is bigger than all keys, it returns size.
	*/
	int64_t left = 0;
	int64_t right = size;
	int64_t mid;
	

	while(left<right) {
    mid = (left + right)/2;   /* ignore possibility of overflow of left+right */
    uint64_t test_mask = (data[mid]>=searchkey)-1; /* boolean 1 becomes mask of 0, boolean 0 becomes mask of 0xFFFFFFFFFFFFFFFF */
    right=(mid&(~test_mask)) | (right&test_mask);
    left=((mid+1)&test_mask) | (left& ~test_mask);
  }
  return right;
}

inline void lower_bound_nb_mask_8x (int64_t *data, int64_t size, int64_t *searchkey, int64_t *right)
{
  /* this binary search variant
	 (a) does no comparisons in the inner loop by using bit masking operations instead
	 (b) doesn't require an exact match; instead it returns the index of the first key >= the search key.
		 That's good in a DB context where we might be doing a range search, and using binary search to
	 identify the first key in the range.
	 (c) If the search key is bigger than all keys, it returns size.
	 (d) does 8 searches at the same time in an interleaved fashion, so that an out-of-order processor
		 can make progress even when some instructions are still waiting for their operands to be ready.

	 Note that we're using the result array as the "right" elements in the search so no need for a return statement
  */
  int64_t left[8] = { 0, 0, 0, 0, 0, 0, 0, 0 };
  int64_t mid[8];
  uint64_t test_mask[8];
  right[0] = right[1] = right[2] = right[3] = right[4] = right[5] = right[6] = right[7] = size;

  while(left[0]<right[0] || left[1]<right[1] || left[2]<right[2] || left[3]<right[3] ||
	left[4]<right[4] || left[5]<right[5] || left[6]<right[6] || left[7]<right[7]) {
    for(int s=0;s<8;s++) {
      /* an optimizing compiler might help here by (a) unrolling the loop, and (b) automatically using SIMD instructions.
	 also, cache misses might be overlapped given an out-of-order processor
       */
      mid[s] = (left[s] + right[s])/2;   /* ignore possibility of overflow of left+right */
      test_mask[s] = (data[mid[s]]>=searchkey[s])-1; /* boolean 1 becomes mask of 0, boolean 0 becomes mask of 0xFFFFFFFFFFFFFFFF */
      right[s]=(mid[s]&(~test_mask[s])) | (right[s]&test_mask[s]);
      left[s]=((mid[s]+1)&test_mask[s]) | (left[s]& ~test_mask[s]);
    }
    /* Don't need to return anything because the result elements are already in the "right" array, which corresponds to
       the result array in the calling context
    */
  }
}

/* The following union type is handy to output the contents of AVX512 data types */
union int8x8 {
	__m512i a;
	int64_t b[8];
};

void printavx (char *name, __m512i v)
{
  union int8x8 n;

  n.a = v;
  printf ("Value in %s is [%ld %ld %ld %ld %ld %ld %ld %ld]\n",
		  name,
		  n.b[0],
		  n.b[1],
		  n.b[2],
		  n.b[3],
		  n.b[4],
		  n.b[5],
		  n.b[6],
		  n.b[7]);
}

inline void lower_bound_nb_mask_8x_AVX512 (int64_t *data, int64_t size, __m512i searchkey, __m512i *result)
{
  /* this binary search variant
	 (a) does no comparisons in the inner loop by using bit masking operations instead
	 (b) doesn't require an exact match; instead it returns the index of the first key >= the search key.
		 That's good in a DB context where we might be doing a range search, and using binary search to
	 identify the first key in the range.
	 (c) If the search key is bigger than all keys, it returns size.
	 (d) does 8 searches at the same time using AVX512 SIMD vectors

	 See https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#techs=AVX_512
	 for documentation of the AVX512 intrinsics

	 Note that we're using the result array as the "right" elements in the search, and that searchkey is being passed
	 as an __m512i value rather than via a pointer.
  */

 __m512i aleft = _mm512_set1_epi64(0);
  __m512i ones = _mm512_set1_epi64(1);
  __m512i amid;
  __m512i aright = _mm512_set1_epi64(size); /* ignore - see Ed post */
  __m512i amask;
  __m512i datavec;
  __mmask8 cmp;

  
  while(_mm512_cmplt_epi64_mask(aleft,aright))
    {
      amid = _mm512_add_epi64 (aleft,aright);
      amid = _mm512_srli_epi64 (amid,1); // divide by 2 */

      datavec = _mm512_i64gather_epi64 (amid, data, 8);
      /*
      printavx("aleft",aleft);
      printavx("aright",aright);
      printavx("amid",amid);
      printavx("searchkey",*searchkey);
      printavx("datavec",datavec);
      */
      
      cmp = _mm512_cmpge_epi64_mask (datavec, searchkey);
      aright = _mm512_mask_blend_epi64 (cmp, aright, amid);
      aleft = _mm512_mask_blend_epi64 (cmp, _mm512_add_epi64(amid,ones), aleft);
    }
  *result = aright;
}


void bulk_binary_search (int64_t *data,
					int64_t size,
					int64_t *searchkeys,
					int64_t numsearches,
					int64_t *results,
					int repeats)
{
  for (int j = 0; j < repeats; j++)
	{
	  /* Function to test a large number of binary searches

		 we might need repeats>1 to make sure the events we're measuring are not dominated by various
		 overheads, particularly for small values of size and/or numsearches

		 we assume that we want exactly "size" searches, where "size" is the length if the searchkeys array
	   */
	  for (int64_t i = 0; i < numsearches; i++)
		{
#ifdef DEBUG
		  printf("Searching for %ld...\n",searchkeys[i]);
#endif

		  // Uncomment one of the following to measure it
		  results[i] = lower_bound (data, size, searchkeys[i]);
		  //results[i] = lower_bound_nb_arithmetic(data,size,searchkeys[i]);
		  //results[i] = lower_bound_nb_mask(data,size,searchkeys[i]);

#ifdef DEBUG
		  printf("Result is %ld\n",results[i]);
#endif
		}
	}
}

void
bulk_binary_search_8x (int64_t *data,
					   int64_t size,
					   int64_t *searchkeys,
					   int64_t numsearches,
					   int64_t *results,
					   int repeats)
{
  register __m512i searchkey_8x;

  for (int j = 0; j < repeats; j++)
	{
	  /* Function to test a large number of binary searches using one of the 8x routines

		 we might need repeats>1 to make sure the events we're measuring are not dominated by various
		 overheads, particularly for small values of size and/or numsearches

		 we assume that we want exactly "size" searches, where "size" is the length if the searchkeys array
	   */
	  int64_t extras = numsearches % 8;
	  for (int64_t i = 0; i < numsearches - extras; i += 8)
		{
#ifdef DEBUG
		  printf("Searching for %ld %ld %ld %ld %ld %ld %ld %ld ...\n",
			 searchkeys[i],searchkeys[i+1],searchkeys[i+2],searchkeys[i+3],searchkeys[i+4],searchkeys[i+5],searchkeys[i+6],searchkeys[i+7]);
#endif

		  // Uncomment one of the following depending on which routine you want to profile

		  // Algorithm A
//		  lower_bound_nb_mask_8x (data, size, &searchkeys[i], &results[i]);

		  // Algorithm B
		  searchkey_8x = _mm512_load_epi64 (&searchkeys[i]);
		  lower_bound_nb_mask_8x_AVX512 (data, size, searchkey_8x, (__m512i * ) & results[i]);

#ifdef DEBUG
		  printf("Result is %ld %ld %ld %ld %ld %ld %ld %ld ...\n",
			 results[i],results[i+1],results[i+2],results[i+3],results[i+4],results[i+5],results[i+6],results[i+7]);
#endif
		}
	  /* a little bit more work if numsearches is not a multiple of 8 */
	  for (int64_t i = numsearches - extras; i < numsearches; i++)
		{

		  results[i] = lower_bound_nb_mask (data, size, searchkeys[i]);

		}

	}
}

int64_t
band_join (int64_t *outer,
		   int64_t outer_size,
		   int64_t *inner,
		   int64_t size,
		   int64_t *outer_results,
		   int64_t *inner_results,
		   int64_t result_size,
		   int64_t bound,
		   int64_t *outer_count)
{
  /* In a band join we want matches within a range of values.  If p is the probe value from the outer table, then all
	 reccords in the inner table with a key in the range [p-bound,p+bound] inclusive should be part of the result.

	 Results are returned via two arrays. outer_results stores the index of the outer table row that matches, and
	 inner_results stores the index of the inner table row that matches.  result_size tells you the size of the
	 output array that has been allocated. You should make sure that you don't exceed this size.  If there are
	 more results than can fit in the result arrays, then return early with just a prefix of the results in the result
	 arrays. The return value of the function should be the number of output results.

	 To do the binary search, you should be calling the routine lower_bound_nb_mask_8x_AVX512 for the bulk of the
	 data, and lower_bound_nb_mask for additional elements when outer_size is not a multiple of 8 (See bulk_binary_search_8x).

	 Once you've found the lower bounds, do the following for each of the 8 search keys in turn:
		scan along the sorted inner array, generating outputs for each match, and making sure not to exceed the output array bounds.

	 This inner scanning code does not have to use SIMD.
  */

  /* YOUR CODE HERE */
  int64_t extras= outer_size % 8;
  int64_t resulti = 0;
  for (int64_t i = 0; i<outer_size - extras; i+=8)
	{
	  /* lower_bound_nb_mask_8x_AVX512 */
	  register __m512i searchkey_8x = _mm512_sub_epi64 (
		  _mm512_load_epi64 (&outer[i]),
		  _mm512_set1_epi64 (bound)
	  );
	  int64_t join[8];
	  lower_bound_nb_mask_8x_AVX512 (inner, size, searchkey_8x, (__m512i *)join);

	  /* lower_bound_nb_mask_8x */
//        int64_t searchkey[8];
//        int64_t join[8];
//        for(int64_t k = 0; k<8; k++){
//            searchkey[k] = outer[i+k] - bound;
//        }
//        lower_bound_nb_mask_8x(inner,size,searchkey,join);

        for(int64_t j =0; j<8; j++)
        {
            int64_t outeri = i+j;
            int64_t inneri = join[j];
            while( (inner[inneri] <= outer[outeri] + bound) && inneri < size)
            {
                inner_results[resulti] = inneri;
                outer_results[resulti] = outeri;
                resulti++;

                if(resulti == result_size)
                {return resulti;  }
                inneri++;
            }
        }
    }
    
     for (int64_t outeri = outer_size- extras; outeri<outer_size; outeri++)
     {
         int64_t inneri = lower_bound_nb_mask(inner,size, outer[outeri]-bound);
         while( (inner[inneri] <= outer[outeri] + bound) && (inneri < size))
            {
                inner_results[resulti] = inneri;
                outer_results[resulti] = outeri;
                resulti++;

                if(resulti == result_size)
                {return resulti;  }
                inneri++;
            }
    }
    return resulti;
     
}

int64_t
band_join_opt (int64_t *outer,
			   int64_t outer_size,
			   int64_t *inner,
			   int64_t size,
			   int64_t *outer_results,
			   int64_t *inner_results,
			   int64_t result_size,
			   int64_t bound,
			   int64_t *outer_count)
{
  /* In a band join we want matches within a range of values.  If p is the probe value from the outer table, then all
	 reccords in the inner table with a key in the range [p-bound,p+bound] inclusive should be part of the result.

	 Results are returned via two arrays. outer_results stores the index of the outer table row that matches, and
	 inner_results stores the index of the inner table row that matches.  result_size tells you the size of the
	 output array that has been allocated. You should make sure that you don't exceed this size.  If there are
	 more results than can fit in the result arrays, then return early with just a prefix of the results in the result
	 arrays. The return value of the function should be the number of output results.

	 To do the binary search, you should be calling the routine lower_bound_nb_mask_8x_AVX512 for the bulk of the
	 data, and lower_bound_nb_mask for additional elements when outer_size is not a multiple of 8 (See bulk_binary_search_8x).

	 One performance overhead of the previous band_join implementation
	 is that one has to test the search key for every
	 inner table record.  In band_join_opt, we avoid testing the search key in the inner loop.
	 To achieve this effect, one needs to know both the lower bounds and the upper bounds for each search...

	 The inner scanning code does not need to use SIMD.

	 This algorithm should be implemented by all three-person groups.  It is optional for two-person groups.
  */

    int64_t outer_index = 0; 
    register __m512i search_8x;
	
	for (int64_t i = 0; i < outer_size - outer_index; i += 8) {  
		int64_t outer_8x[8];

		int i = 0;
		while (i < 8) {
			outer_8x[i] = outer[outer_index + i] - bound;
			i +=  1;
		}
		i = 0;
		search_8x = _mm512_load_epi64(&outer_8x);

		int64_t lower_bound_index_8x[8];
		lower_bound_nb_mask_8x_AVX512(inner, size, search_8x, (__m512i*) &lower_bound_index_8x);

		while (i < 8) {
			if (lower_bound_index_8x[i] < size) {
				int64_t upper_bound_index = lower_bound_nb_mask(inner, size, outer[outer_index + i] + bound);
				(*outer_count)++;
				for (int j = lower_bound_index_8x[i]; j < upper_bound_index; j++) {
					if (result_size < idx) {
						return result_size;
					}
					else {
						outer_results[idx] = outer_index; 
						inner_results[idx] = j; 
						idx++;
					}
				}            
			}
			i += 1;
		}
		outer_index += 8;
	}


	for (int outeri = outer_index; outeri < outer_size; outeri++) {
		int64_t search_key = outer[outer_index] - bound; 
		int64_t lower_bound_index = lower_bound_nb_mask(inner, size, search_key);

		if(lower_bound_index < size) {
			int64_t upper_bound_index = lower_bound_nb_mask(inner, size, outer[outer_index] + bound);
			(*outer_count)++;
			for (int i = lower_bound_index; i < upper_bound_index; i++) {
				if (result_size < idx) {
					return result_size;
				}
				else {
					outer_results[idx] = outer_index; 
					inner_results[idx] = i; 
					idx++;
				}
			}
		}
		outer_index++;
	}

	return idx;
}

int
main (int argc, char *argv[])
{
  long long counter;
  int64_t arraysize, outer_size, result_size;
  int64_t outer_count = 0;
  int64_t bound;
  int64_t * data, *queries, *results;
  int ret;
  struct timeval before, after;
  int repeats;
  int64_t total_results;

  // band-join arrays
  int64_t * outer, *outer_results, *inner_results;

  if (argc >= 5)
	{
	  arraysize = atoi (argv[1]);
	  outer_size = atoi (argv[2]);
	  result_size = atoi (argv[3]);
	  bound = atoi (argv[4]);
	}
  else
	{
	  fprintf (stderr, "Usage: db4112 inner_size outer_size result_size bound <repeats>\n");
	  exit (EXIT_FAILURE);
	}

  if (argc >= 6)
	repeats = atoi (argv[5]);
  else
	{
	  repeats = 1;
	}

  /* allocate the array and the queries for searching */
  ret = posix_memalign ((void **)&data, 64, arraysize * sizeof (int64_t));
  if (ret)
	{
	  fprintf (stderr, "Memory allocation error.\n");
	  exit (EXIT_FAILURE);
	}
  ret = posix_memalign ((void **)&queries, 64, arraysize * sizeof (int64_t));
  if (ret)
	{
	  fprintf (stderr, "Memory allocation error.\n");
	  exit (EXIT_FAILURE);
	}
  ret = posix_memalign ((void **)&results, 64, arraysize * sizeof (int64_t));
  if (ret)
	{
	  fprintf (stderr, "Memory allocation error.\n");
	  exit (EXIT_FAILURE);
	}

  /* allocate the outer array and output arrays for band-join */
  ret = posix_memalign ((void **)&outer, 64, outer_size * sizeof (int64_t));
  if (ret)
	{
	  fprintf (stderr, "Memory allocation error.\n");
	  exit (EXIT_FAILURE);
	}
  ret = posix_memalign ((void **)&outer_results, 64, result_size * sizeof (int64_t));
  if (ret)
	{
	  fprintf (stderr, "Memory allocation error.\n");
	  exit (EXIT_FAILURE);
	}
  ret = posix_memalign ((void **)&inner_results, 64, result_size * sizeof (int64_t));
  if (ret)
	{
	  fprintf (stderr, "Memory allocation error.\n");
	  exit (EXIT_FAILURE);
	}


  /* code to initialize data structures goes here so that it is not included in the timing measurement */
  init (data, queries, arraysize);
  band_init (outer, outer_size);

#ifdef DEBUG
  /* show the arrays */
  printf("data: ");
  for(int64_t i=0;i<arraysize;i++) printf("%ld ",data[i]);
  printf("\n");
  printf("queries: ");
  for(int64_t i=0;i<arraysize;i++) printf("%ld ",queries[i]);
  printf("\n");
  printf("outer: ");
  for(int64_t i=0;i<outer_size;i++) printf("%ld ",outer[i]);
  printf("\n");
#endif


  /* now measure... */

  gettimeofday (&before, NULL);

  /* the code that you want to measure goes here; make a function call */
  bulk_binary_search (data, arraysize, queries, arraysize, results, repeats);

  gettimeofday (&after, NULL);
  printf ("Time in bulk_binary_search loop is %ld microseconds or %f microseconds per search\n",
		  (after.tv_sec - before.tv_sec) * 1000000 + (after.tv_usec - before.tv_usec),
		  1.0 * ((after.tv_sec - before.tv_sec) * 1000000 + (after.tv_usec - before.tv_usec)) / arraysize / repeats);

  gettimeofday (&before, NULL);

  /* the code that you want to measure goes here; make a function call */
  bulk_binary_search_8x (data, arraysize, queries, arraysize, results, repeats);

  gettimeofday (&after, NULL);
  printf ("Time in bulk_binary_search_8x loop is %ld microseconds or %f microseconds per search\n",
		  (after.tv_sec - before.tv_sec) * 1000000 + (after.tv_usec - before.tv_usec),
		  1.0 * ((after.tv_sec - before.tv_sec) * 1000000 + (after.tv_usec - before.tv_usec)) / arraysize / repeats);

  gettimeofday (&before, NULL);

  /* the code that you want to measure goes here; make a function call */
//   total_results = band_join_opt (outer, outer_size, data, arraysize, outer_results, inner_results, result_size, bound);

//   gettimeofday (&after, NULL);
//   printf ("Band join result size is %ld with an average of %f matches per output record\n",
// 		  total_results,
// 		  1.0 * total_results / (1.0 + outer_results[total_results - 1]));
//   printf ("Time in band_join loop is %ld microseconds or %f microseconds per outer record\n",
// 		  (after.tv_sec - before.tv_sec) * 1000000 + (after.tv_usec - before.tv_usec),
// 		  1.0 * ((after.tv_sec - before.tv_sec) * 1000000 + (after.tv_usec - before.tv_usec)) / (1.0 + outer_results[total_results - 1]));

	total_results=band_join_opt(outer, outer_size, data, arraysize, outer_results, inner_results, result_size, bound, &outer_count);
                  
    gettimeofday(&after,NULL);

    printf("Band join result size is %ld with an average of %f matches per outer record\n",total_results, 1.0*total_results/outer_count);
    printf("Time in band_join loop is %ld microseconds or %f microseconds per outer record\n", (after.tv_sec-before.tv_sec)*1000000+(after.tv_usec-before.tv_usec), 1.0*((after.tv_sec-before.tv_sec)*1000000+(after.tv_usec-before.tv_usec))/outer_count);


#ifdef DEBUG
  /* show the band_join results */
  printf("band_join results: ");
  for(int64_t i=0;i<total_results;i++) printf("(%ld,%ld) ",outer_results[i],inner_results[i]);
  printf("\n");
#endif

}
