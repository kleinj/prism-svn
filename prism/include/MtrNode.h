/* DO NOT EDIT THIS FILE - it is machine generated */
#include <jni.h>
/* Header for class jdd_MtrNode */

#ifndef _Included_jdd_MtrNode
#define _Included_jdd_MtrNode
#ifdef __cplusplus
extern "C" {
#endif
/*
 * Class:     jdd_MtrNode
 * Method:    DDM_MakeGroup
 * Signature: (ZII)J
 */
JNIEXPORT jlong JNICALL Java_jdd_MtrNode_DDM_1MakeGroup
  (JNIEnv *, jclass, jboolean, jint, jint);

/*
 * Class:     jdd_MtrNode
 * Method:    DDM_AddChild
 * Signature: (JJ)V
 */
JNIEXPORT void JNICALL Java_jdd_MtrNode_DDM_1AddChild
  (JNIEnv *, jclass, jlong, jlong);

/*
 * Class:     jdd_MtrNode
 * Method:    DDM_CuddSetTree
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_jdd_MtrNode_DDM_1CuddSetTree
  (JNIEnv *, jclass, jlong);

/*
 * Class:     jdd_MtrNode
 * Method:    DDM_FreeTree
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_jdd_MtrNode_DDM_1FreeTree
  (JNIEnv *, jclass, jlong);

#ifdef __cplusplus
}
#endif
#endif
