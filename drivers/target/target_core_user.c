/*
 * Copyright (C) 2013 Shaohua Li <shli@kernel.org>
 * Copyright (C) 2014 Red Hat, Inc.
 * Copyright (C) 2015 Arrikto, Inc.
 * Copyright (C) 2017 Chinamobile, Inc.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms and conditions of the GNU General Public License,
 * version 2, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin St - Fifth Floor, Boston, MA 02110-1301 USA.
 */

#include <linux/spinlock.h>
#include <linux/module.h>
#include <linux/idr.h>
#include <linux/kernel.h>
#include <linux/timer.h>
#include <linux/parser.h>
#include <linux/vmalloc.h>
#include <linux/uio_driver.h>
#include <linux/radix-tree.h>
#include <linux/stringify.h>
#include <linux/bitops.h>
#include <linux/highmem.h>
#include <linux/configfs.h>
#include <linux/mutex.h>
#include <linux/workqueue.h>
#include <net/genetlink.h>
#include <scsi/scsi_common.h>
#include <scsi/scsi_proto.h>
#include <target/target_core_base.h>
#include <target/target_core_fabric.h>
#include <target/target_core_backend.h>

#include <linux/target_core_user.h>
#include "target_core_pr.h"

/*
 * Define a shared-memory interface for LIO to pass SCSI commands and
 * data to userspace for processing. This is to allow backends that
 * are too complex for in-kernel support to be possible.
 *
 * It uses the UIO framework to do a lot of the device-creation and
 * introspection work for us.
 *
 * See the .h file for how the ring is laid out. Note that while the
 * command ring is defined, the particulars of the data area are
 * not. Offset values in the command entry point to other locations
 * internal to the mmap()ed area. There is separate space outside the
 * command ring for data buffers. This leaves maximum flexibility for
 * moving buffer allocations, or even page flipping or other
 * allocation techniques, without altering the command ring layout.
 *
 * SECURITY:
 * The user process must be assumed to be malicious. There's no way to
 * prevent it breaking the command ring protocol if it wants, but in
 * order to prevent other issues we must only ever read *data* from
 * the shared memory area, not offsets or sizes. This applies to
 * command ring entries as well as the mailbox. Extra code needed for
 * this may have a 'UAM' comment.
 */

#define TCMU_TIME_OUT (30 * MSEC_PER_SEC)

/* For cmd area, the size is fixed 8MB */
#define CMDR_SIZE (8 * 1024 * 1024)

/*
 * For data area, the block size is PAGE_SIZE and
 * the total size is 256K * PAGE_SIZE.
 */
#define DATA_BLOCK_SIZE PAGE_SIZE
#define DATA_BLOCK_SHIFT PAGE_SHIFT
#define DATA_BLOCK_BITS_DEF (256 * 1024)
#define DATA_SIZE (DATA_BLOCK_BITS * DATA_BLOCK_SIZE)

#define TCMU_MBS_TO_BLOCKS(_mbs) (_mbs << (20 - DATA_BLOCK_SHIFT))
#define TCMU_BLOCKS_TO_MBS(_blocks) (_blocks >> (20 - DATA_BLOCK_SHIFT))

/* The total size of the ring is 8M + 256K * PAGE_SIZE */
#define TCMU_RING_SIZE (CMDR_SIZE + DATA_SIZE)

/*
 * Default number of global data blocks(512K * PAGE_SIZE)
 * when the unmap thread will be started.
 */
#define TCMU_GLOBAL_MAX_BLOCKS_DEF (512 * 1024)

#define TCMU_PR_INFO_XATTR_VERS		1
#define TCMU_PR_INFO_XATTR_VAL_SCSI2_RSV_ABSENT		"No SPC-2 Reservation holder"
#define TCMU_PR_INFO_XATTR_VAL_SCSI3_RSV_ABSENT		"No SPC-3 Reservation holder"

#define TCMU_PR_IT_NEXUS_MAXLEN		484

#define TCMU_PR_INFO_XATTR_FIELD_VER		0
#define TCMU_PR_INFO_XATTR_FIELD_SEQ		1
#define TCMU_PR_INFO_XATTR_FIELD_SCSI2_RSV	2
#define TCMU_PR_INFO_XATTR_FIELD_GEN		3
#define TCMU_PR_INFO_XATTR_FIELD_SCSI3_RSV	4
#define TCMU_PR_INFO_XATTR_FIELD_NUM_REGS	5
#define TCMU_PR_INFO_XATTR_FIELD_REGS_START	6

/* don't allow encoded PR info to exceed 8K */
#define TCMU_PR_INFO_XATTR_MAX_SIZE 8192

#define TCMU_PR_INFO_XATTR_ENCODED_SCSI2_RSV_MAXLEN		\
	(TCMU_PR_IT_NEXUS_MAXLEN + sizeof("\n"))

#define TCMU_PR_INFO_XATTR_ENCODED_PR_RSV_MAXLEN		\
	((sizeof("0x") + sizeof(u64) * 2) + sizeof(" ") +	\
	 TCMU_PR_IT_NEXUS_MAXLEN + sizeof(" ") +		\
	 (sizeof("0x") + sizeof(u64) * 2) + sizeof("\n"))

#define TCMU_PR_INFO_XATTR_ENCODED_PR_REG_MAXLEN		\
	((sizeof("0x") + sizeof(u64) * 2) + sizeof(" ") +	\
	 TCMU_PR_IT_NEXUS_MAXLEN + sizeof("\n"))

#define TCMU_PR_INFO_XATTR_ENCODED_MAXLEN(_num_regs)			\
	 ((sizeof("0x") + sizeof(u32) * 2) + sizeof("\n") +		\
	 (sizeof("0x") + sizeof(u32) * 2) + sizeof("\n") +		\
	 TCMU_PR_INFO_XATTR_ENCODED_SCSI2_RSV_MAXLEN +		\
	 (sizeof("0x") + sizeof(u32) * 2) + sizeof("\n") +		\
	 TCMU_PR_INFO_XATTR_ENCODED_PR_RSV_MAXLEN +			\
	 (sizeof("0x") + sizeof(u32) * 2) + sizeof("\n") +		\
	 (TCMU_PR_INFO_XATTR_ENCODED_PR_REG_MAXLEN * _num_regs) +	\
	 sizeof("\0"))

static u8 tcmu_kern_cmd_reply_supported;

static struct device *tcmu_root_device;

struct tcmu_hba {
	u32 host_id;
};

#define TCMU_CONFIG_LEN 256

struct tcmu_nl_cmd {
	/* wake up thread waiting for reply */
	struct completion complete;
	int cmd;
	int status;
};

/* This struct help to store the string buffer which contain
 * Persistent Reservation info record from the device metadata.
 */
struct tcmu_dev_pr_info {
	struct mutex pr_info_lock;
	char *pr_info_buf;
	};

/*
 * Persistent reservation info. This structure is converted to and from a
 * string in a TCMU device storage (for example, if we use a RBD, we store such
 * a string in it's metadata) which contain PR information.
 */
struct tcmu_pr_rsv {
	u64 key;	/* registered key */
	/*
	 * I-T nexus for reservation. Separate to reg, so that all_tg_pt flag
	 * can be supported in future.
	 */
	char it_nexus[TCMU_PR_IT_NEXUS_MAXLEN];
	int type;		/* PR_TYPE */
	/* scope is always PR_SCOPE_LU_SCOPE */
	};

struct tcmu_dev {
	struct list_head node;
	struct kref kref;

	struct se_device se_dev;

	char *name;
	struct se_hba *hba;

#define TCMU_DEV_BIT_OPEN 0
#define TCMU_DEV_BIT_BROKEN 1
#define TCMU_DEV_BIT_BLOCKED 2
	unsigned long flags;

	struct uio_info uio_info;

	struct inode *inode;

	struct tcmu_mailbox *mb_addr;
	size_t dev_size;
	u32 cmdr_size;
	u32 cmdr_last_cleaned;
	/* Offset of data area from start of mb */
	/* Must add data_off and mb_addr to get the address */
	size_t data_off;
	size_t data_size;
	uint32_t max_blocks;
	size_t ring_size;

	struct mutex cmdr_lock;
	struct list_head cmdr_queue;

	uint32_t dbi_max;
	uint32_t dbi_thresh;
	unsigned long *data_bitmap;
	struct radix_tree_root data_blocks;

	struct idr commands;

	struct timer_list cmd_timer;
	unsigned int cmd_time_out;

	struct timer_list qfull_timer;
	int qfull_time_out;

	struct list_head timedout_entry;

	spinlock_t nl_cmd_lock;
	struct tcmu_nl_cmd curr_nl_cmd;
	/* wake up threads waiting on curr_nl_cmd */
	wait_queue_head_t nl_cmd_wq;

	char dev_config[TCMU_CONFIG_LEN];

	int nl_reply_supported;
	struct tcmu_dev_pr_info pr_info;
};

#define TCMU_DEV(_se_dev) container_of(_se_dev, struct tcmu_dev, se_dev)

#define CMDR_OFF sizeof(struct tcmu_mailbox)

struct tcmu_cmd {
	struct se_cmd *se_cmd;
	struct tcmu_dev *tcmu_dev;
	struct list_head cmdr_queue_entry;

	uint16_t cmd_id;

	/* Can't use se_cmd when cleaning up expired cmds, because if
	   cmd has been completed then accessing se_cmd is off limits */
	uint32_t dbi_cnt;
	uint32_t dbi_cur;
	uint32_t *dbi;

	unsigned long deadline;

#define TCMU_CMD_BIT_EXPIRED 0
	unsigned long flags;
};

/*
 * I-T nexus for SCSI2 (RESERVE/RELEASE) reservation.
 */
struct tcmu_scsi2_rsv {
	char it_nexus[TCMU_PR_IT_NEXUS_MAXLEN];
	};

struct tcmu_pr_reg {
	struct list_head regs_node;
	u64 key;	/* registered key */
	/* I-T nexus for registration */
	char it_nexus[TCMU_PR_IT_NEXUS_MAXLEN];
};

/*
 * To avoid dead lock the mutex lock order should always be:
 *
 * mutex_lock(&root_udev_mutex);
 * ...
 * mutex_lock(&tcmu_dev->cmdr_lock);
 * mutex_unlock(&tcmu_dev->cmdr_lock);
 * ...
 * mutex_unlock(&root_udev_mutex);
 */
static DEFINE_MUTEX(root_udev_mutex);
static LIST_HEAD(root_udev);

static DEFINE_SPINLOCK(timed_out_udevs_lock);
static LIST_HEAD(timed_out_udevs);

static struct kmem_cache *tcmu_cmd_cache;

static atomic_t global_db_count = ATOMIC_INIT(0);
static struct delayed_work tcmu_unmap_work;
static int tcmu_global_max_blocks = TCMU_GLOBAL_MAX_BLOCKS_DEF;

static int tcmu_set_global_max_data_area(const char *str,
					 const struct kernel_param *kp)
{
	int ret, max_area_mb;

	ret = kstrtoint(str, 10, &max_area_mb);
	if (ret)
		return -EINVAL;

	if (max_area_mb <= 0) {
		pr_err("global_max_data_area must be larger than 0.\n");
		return -EINVAL;
	}

	tcmu_global_max_blocks = TCMU_MBS_TO_BLOCKS(max_area_mb);
	if (atomic_read(&global_db_count) > tcmu_global_max_blocks)
		schedule_delayed_work(&tcmu_unmap_work, 0);
	else
		cancel_delayed_work_sync(&tcmu_unmap_work);

	return 0;
}

static int tcmu_get_global_max_data_area(char *buffer,
					 const struct kernel_param *kp)
{
	return sprintf(buffer, "%d", TCMU_BLOCKS_TO_MBS(tcmu_global_max_blocks));
}

static const struct kernel_param_ops tcmu_global_max_data_area_op = {
	.set = tcmu_set_global_max_data_area,
	.get = tcmu_get_global_max_data_area,
};

module_param_cb(global_max_data_area_mb, &tcmu_global_max_data_area_op, NULL,
		S_IWUSR | S_IRUGO);
MODULE_PARM_DESC(global_max_data_area_mb,
		 "Max MBs allowed to be allocated to all the tcmu device's "
		 "data areas.");

/* multicast group */
enum tcmu_multicast_groups {
	TCMU_MCGRP_CONFIG,
};

static const struct genl_multicast_group tcmu_mcgrps[] = {
	[TCMU_MCGRP_CONFIG] = { .name = "config", },
};

static struct nla_policy tcmu_attr_policy[TCMU_ATTR_MAX+1] = {
	[TCMU_ATTR_DEVICE]	= { .type = NLA_STRING },
	[TCMU_ATTR_MINOR]	= { .type = NLA_U32 },
	[TCMU_ATTR_CMD_STATUS]	= { .type = NLA_S32 },
	[TCMU_ATTR_DEVICE_ID]	= { .type = NLA_U32 },
	[TCMU_ATTR_SUPP_KERN_CMD_REPLY] = { .type = NLA_U8 },
};

static int tcmu_genl_cmd_done(struct genl_info *info, int completed_cmd)
{
	struct se_device *dev;
	struct tcmu_dev *udev;
	struct tcmu_nl_cmd *nl_cmd;
	int dev_id, rc, ret = 0;
	bool is_removed = (completed_cmd == TCMU_CMD_REMOVED_DEVICE);

	if (!info->attrs[TCMU_ATTR_CMD_STATUS] ||
	    !info->attrs[TCMU_ATTR_DEVICE_ID]) {
		printk(KERN_ERR "TCMU_ATTR_CMD_STATUS or TCMU_ATTR_DEVICE_ID not set, doing nothing\n");
                return -EINVAL;
        }

	dev_id = nla_get_u32(info->attrs[TCMU_ATTR_DEVICE_ID]);
	rc = nla_get_s32(info->attrs[TCMU_ATTR_CMD_STATUS]);

	dev = target_find_device(dev_id, !is_removed);
	if (!dev) {
		printk(KERN_ERR "tcmu nl cmd %u/%u completion could not find device with dev id %u.\n",
		       completed_cmd, rc, dev_id);
		return -ENODEV;
	}
	udev = TCMU_DEV(dev);

	spin_lock(&udev->nl_cmd_lock);
	nl_cmd = &udev->curr_nl_cmd;

	pr_debug("genl cmd done got id %d curr %d done %d rc %d\n", dev_id,
		 nl_cmd->cmd, completed_cmd, rc);

	if (nl_cmd->cmd != completed_cmd) {
		printk(KERN_ERR "Mismatched commands (Expecting reply for %d. Current %d).\n",
		       completed_cmd, nl_cmd->cmd);
		ret = -EINVAL;
	} else {
		nl_cmd->status = rc;
	}

	spin_unlock(&udev->nl_cmd_lock);
	if (!is_removed)
		 target_undepend_item(&dev->dev_group.cg_item);
	if (!ret)
		complete(&nl_cmd->complete);
	return ret;
}

static int tcmu_genl_rm_dev_done(struct sk_buff *skb, struct genl_info *info)
{
	return tcmu_genl_cmd_done(info, TCMU_CMD_REMOVED_DEVICE);
}

static int tcmu_genl_add_dev_done(struct sk_buff *skb, struct genl_info *info)
{
	return tcmu_genl_cmd_done(info, TCMU_CMD_ADDED_DEVICE);
}

static int tcmu_genl_reconfig_dev_done(struct sk_buff *skb,
				       struct genl_info *info)
{
	return tcmu_genl_cmd_done(info, TCMU_CMD_RECONFIG_DEVICE);
}

static int tcmu_genl_set_features(struct sk_buff *skb, struct genl_info *info)
{
	if (info->attrs[TCMU_ATTR_SUPP_KERN_CMD_REPLY]) {
		tcmu_kern_cmd_reply_supported  =
			nla_get_u8(info->attrs[TCMU_ATTR_SUPP_KERN_CMD_REPLY]);
		printk(KERN_INFO "tcmu daemon: command reply support %u.\n",
		       tcmu_kern_cmd_reply_supported);
	}

	return 0;
}

static const struct genl_ops tcmu_genl_ops[] = {
	{
		.cmd	= TCMU_CMD_SET_FEATURES,
		.flags	= GENL_ADMIN_PERM,
		.policy	= tcmu_attr_policy,
		.doit	= tcmu_genl_set_features,
	},
	{
		.cmd	= TCMU_CMD_ADDED_DEVICE_DONE,
		.flags	= GENL_ADMIN_PERM,
		.policy	= tcmu_attr_policy,
		.doit	= tcmu_genl_add_dev_done,
	},
	{
		.cmd	= TCMU_CMD_REMOVED_DEVICE_DONE,
		.flags	= GENL_ADMIN_PERM,
		.policy	= tcmu_attr_policy,
		.doit	= tcmu_genl_rm_dev_done,
	},
	{
		.cmd	= TCMU_CMD_RECONFIG_DEVICE_DONE,
		.flags	= GENL_ADMIN_PERM,
		.policy	= tcmu_attr_policy,
		.doit	= tcmu_genl_reconfig_dev_done,
	},
};

/* Our generic netlink family */
static struct genl_family tcmu_genl_family __ro_after_init = {
	.module = THIS_MODULE,
	.hdrsize = 0,
	.name = "TCM-USER",
	.version = 2,
	.maxattr = TCMU_ATTR_MAX,
	.mcgrps = tcmu_mcgrps,
	.n_mcgrps = ARRAY_SIZE(tcmu_mcgrps),
	.netnsok = true,
	.ops = tcmu_genl_ops,
	.n_ops = ARRAY_SIZE(tcmu_genl_ops),
};

#define tcmu_cmd_set_dbi_cur(cmd, index) ((cmd)->dbi_cur = (index))
#define tcmu_cmd_reset_dbi_cur(cmd) tcmu_cmd_set_dbi_cur(cmd, 0)
#define tcmu_cmd_set_dbi(cmd, index) ((cmd)->dbi[(cmd)->dbi_cur++] = (index))
#define tcmu_cmd_get_dbi(cmd) ((cmd)->dbi[(cmd)->dbi_cur++])

static void tcmu_cmd_free_data(struct tcmu_cmd *tcmu_cmd, uint32_t len)
{
	struct tcmu_dev *udev = tcmu_cmd->tcmu_dev;
	uint32_t i;

	for (i = 0; i < len; i++)
		clear_bit(tcmu_cmd->dbi[i], udev->data_bitmap);
}

static inline bool tcmu_get_empty_block(struct tcmu_dev *udev,
					struct tcmu_cmd *tcmu_cmd)
{
	struct page *page;
	int ret, dbi;

	dbi = find_first_zero_bit(udev->data_bitmap, udev->dbi_thresh);
	if (dbi == udev->dbi_thresh)
		return false;

	page = radix_tree_lookup(&udev->data_blocks, dbi);
	if (!page) {
		if (atomic_add_return(1, &global_db_count) >
				      tcmu_global_max_blocks)
			schedule_delayed_work(&tcmu_unmap_work, 0);

		/* try to get new page from the mm */
		page = alloc_page(GFP_KERNEL);
		if (!page)
			goto err_alloc;

		ret = radix_tree_insert(&udev->data_blocks, dbi, page);
		if (ret)
			goto err_insert;
	}

	if (dbi > udev->dbi_max)
		udev->dbi_max = dbi;

	set_bit(dbi, udev->data_bitmap);
	tcmu_cmd_set_dbi(tcmu_cmd, dbi);

	return true;
err_insert:
	__free_page(page);
err_alloc:
	atomic_dec(&global_db_count);
	return false;
}

static bool tcmu_get_empty_blocks(struct tcmu_dev *udev,
				  struct tcmu_cmd *tcmu_cmd)
{
	int i;

	for (i = tcmu_cmd->dbi_cur; i < tcmu_cmd->dbi_cnt; i++) {
		if (!tcmu_get_empty_block(udev, tcmu_cmd))
			return false;
	}
	return true;
}

static inline struct page *
tcmu_get_block_page(struct tcmu_dev *udev, uint32_t dbi)
{
	return radix_tree_lookup(&udev->data_blocks, dbi);
}

static inline void tcmu_free_cmd(struct tcmu_cmd *tcmu_cmd)
{
	kfree(tcmu_cmd->dbi);
	kmem_cache_free(tcmu_cmd_cache, tcmu_cmd);
}

static inline size_t tcmu_cmd_get_data_length(struct tcmu_cmd *tcmu_cmd)
{
	struct se_cmd *se_cmd = tcmu_cmd->se_cmd;
	size_t data_length = round_up(se_cmd->data_length, DATA_BLOCK_SIZE);

	if (se_cmd->se_cmd_flags & SCF_BIDI) {
		BUG_ON(!(se_cmd->t_bidi_data_sg && se_cmd->t_bidi_data_nents));
		data_length += round_up(se_cmd->t_bidi_data_sg->length,
				DATA_BLOCK_SIZE);
	}

	return data_length;
}

static inline uint32_t tcmu_cmd_get_block_cnt(struct tcmu_cmd *tcmu_cmd)
{
	size_t data_length = tcmu_cmd_get_data_length(tcmu_cmd);

	return data_length / DATA_BLOCK_SIZE;
}

static struct tcmu_cmd *tcmu_alloc_cmd(struct se_cmd *se_cmd)
{
	struct se_device *se_dev = se_cmd->se_dev;
	struct tcmu_dev *udev = TCMU_DEV(se_dev);
	struct tcmu_cmd *tcmu_cmd;

	tcmu_cmd = kmem_cache_zalloc(tcmu_cmd_cache, GFP_KERNEL);
	if (!tcmu_cmd)
		return NULL;

	INIT_LIST_HEAD(&tcmu_cmd->cmdr_queue_entry);
	tcmu_cmd->se_cmd = se_cmd;
	tcmu_cmd->tcmu_dev = udev;

	tcmu_cmd_reset_dbi_cur(tcmu_cmd);
	tcmu_cmd->dbi_cnt = tcmu_cmd_get_block_cnt(tcmu_cmd);
	tcmu_cmd->dbi = kcalloc(tcmu_cmd->dbi_cnt, sizeof(uint32_t),
				GFP_KERNEL);
	if (!tcmu_cmd->dbi) {
		kmem_cache_free(tcmu_cmd_cache, tcmu_cmd);
		return NULL;
	}

	return tcmu_cmd;
}

static inline void tcmu_flush_dcache_range(void *vaddr, size_t size)
{
	unsigned long offset = offset_in_page(vaddr);
	void *start = vaddr - offset;

	size = round_up(size+offset, PAGE_SIZE);

	while (size) {
		flush_dcache_page(virt_to_page(start));
		start += PAGE_SIZE;
		size -= PAGE_SIZE;
	}
}

/*
 * Some ring helper functions. We don't assume size is a power of 2 so
 * we can't use circ_buf.h.
 */
static inline size_t spc_used(size_t head, size_t tail, size_t size)
{
	int diff = head - tail;

	if (diff >= 0)
		return diff;
	else
		return size + diff;
}

static inline size_t spc_free(size_t head, size_t tail, size_t size)
{
	/* Keep 1 byte unused or we can't tell full from empty */
	return (size - spc_used(head, tail, size) - 1);
}

static inline size_t head_to_end(size_t head, size_t size)
{
	return size - head;
}

static inline void new_iov(struct iovec **iov, int *iov_cnt)
{
	struct iovec *iovec;

	if (*iov_cnt != 0)
		(*iov)++;
	(*iov_cnt)++;

	iovec = *iov;
	memset(iovec, 0, sizeof(struct iovec));
}

#define UPDATE_HEAD(head, used, size) smp_store_release(&head, ((head % size) + used) % size)

/* offset is relative to mb_addr */
static inline size_t get_block_offset_user(struct tcmu_dev *dev,
		int dbi, int remaining)
{
	return dev->data_off + dbi * DATA_BLOCK_SIZE +
		DATA_BLOCK_SIZE - remaining;
}

static inline size_t iov_tail(struct iovec *iov)
{
	return (size_t)iov->iov_base + iov->iov_len;
}

static void scatter_data_area(struct tcmu_dev *udev,
	struct tcmu_cmd *tcmu_cmd, struct scatterlist *data_sg,
	unsigned int data_nents, struct iovec **iov,
	int *iov_cnt, bool copy_data)
{
	int i, dbi;
	int block_remaining = 0;
	void *from, *to = NULL;
	size_t copy_bytes, to_offset, offset;
	struct scatterlist *sg;
	struct page *page;

	for_each_sg(data_sg, sg, data_nents, i) {
		int sg_remaining = sg->length;
		from = kmap_atomic(sg_page(sg)) + sg->offset;
		while (sg_remaining > 0) {
			if (block_remaining == 0) {
				if (to)
					kunmap_atomic(to);

				block_remaining = DATA_BLOCK_SIZE;
				dbi = tcmu_cmd_get_dbi(tcmu_cmd);
				page = tcmu_get_block_page(udev, dbi);
				to = kmap_atomic(page);
			}

			/*
			 * Covert to virtual offset of the ring data area.
			 */
			to_offset = get_block_offset_user(udev, dbi,
					block_remaining);

			/*
			 * The following code will gather and map the blocks
			 * to the same iovec when the blocks are all next to
			 * each other.
			 */
			copy_bytes = min_t(size_t, sg_remaining,
					block_remaining);
			if (*iov_cnt != 0 &&
			    to_offset == iov_tail(*iov)) {
				/*
				 * Will append to the current iovec, because
				 * the current block page is next to the
				 * previous one.
				 */
				(*iov)->iov_len += copy_bytes;
			} else {
				/*
				 * Will allocate a new iovec because we are
				 * first time here or the current block page
				 * is not next to the previous one.
				 */
				new_iov(iov, iov_cnt);
				(*iov)->iov_base = (void __user *)to_offset;
				(*iov)->iov_len = copy_bytes;
			}

			if (copy_data) {
				offset = DATA_BLOCK_SIZE - block_remaining;
				memcpy(to + offset,
				       from + sg->length - sg_remaining,
				       copy_bytes);
				tcmu_flush_dcache_range(to, copy_bytes);
			}

			sg_remaining -= copy_bytes;
			block_remaining -= copy_bytes;
		}
		kunmap_atomic(from - sg->offset);
	}

	if (to)
		kunmap_atomic(to);
}

static void gather_data_area(struct tcmu_dev *udev, struct tcmu_cmd *cmd,
			     bool bidi)
{
	struct se_cmd *se_cmd = cmd->se_cmd;
	int i, dbi;
	int block_remaining = 0;
	void *from = NULL, *to;
	size_t copy_bytes, offset;
	struct scatterlist *sg, *data_sg;
	struct page *page;
	unsigned int data_nents;
	uint32_t count = 0;

	if (!bidi) {
		data_sg = se_cmd->t_data_sg;
		data_nents = se_cmd->t_data_nents;
	} else {

		/*
		 * For bidi case, the first count blocks are for Data-Out
		 * buffer blocks, and before gathering the Data-In buffer
		 * the Data-Out buffer blocks should be discarded.
		 */
		count = DIV_ROUND_UP(se_cmd->data_length, DATA_BLOCK_SIZE);

		data_sg = se_cmd->t_bidi_data_sg;
		data_nents = se_cmd->t_bidi_data_nents;
	}

	tcmu_cmd_set_dbi_cur(cmd, count);

	for_each_sg(data_sg, sg, data_nents, i) {
		int sg_remaining = sg->length;
		to = kmap_atomic(sg_page(sg)) + sg->offset;
		while (sg_remaining > 0) {
			if (block_remaining == 0) {
				if (from)
					kunmap_atomic(from);

				block_remaining = DATA_BLOCK_SIZE;
				dbi = tcmu_cmd_get_dbi(cmd);
				page = tcmu_get_block_page(udev, dbi);
				from = kmap_atomic(page);
			}
			copy_bytes = min_t(size_t, sg_remaining,
					block_remaining);
			offset = DATA_BLOCK_SIZE - block_remaining;
			tcmu_flush_dcache_range(from, copy_bytes);
			memcpy(to + sg->length - sg_remaining, from + offset,
					copy_bytes);

			sg_remaining -= copy_bytes;
			block_remaining -= copy_bytes;
		}
		kunmap_atomic(to - sg->offset);
	}
	if (from)
		kunmap_atomic(from);
}

static inline size_t spc_bitmap_free(unsigned long *bitmap, uint32_t thresh)
{
	return thresh - bitmap_weight(bitmap, thresh);
}

/*
 * We can't queue a command until we have space available on the cmd ring *and*
 * space available on the data area.
 *
 * Called with ring lock held.
 */
static bool is_ring_space_avail(struct tcmu_dev *udev, struct tcmu_cmd *cmd,
		size_t cmd_size, size_t data_needed)
{
	struct tcmu_mailbox *mb = udev->mb_addr;
	uint32_t blocks_needed = (data_needed + DATA_BLOCK_SIZE - 1)
				/ DATA_BLOCK_SIZE;
	size_t space, cmd_needed;
	u32 cmd_head;

	tcmu_flush_dcache_range(mb, sizeof(*mb));

	cmd_head = mb->cmd_head % udev->cmdr_size; /* UAM */

	/*
	 * If cmd end-of-ring space is too small then we need space for a NOP plus
	 * original cmd - cmds are internally contiguous.
	 */
	if (head_to_end(cmd_head, udev->cmdr_size) >= cmd_size)
		cmd_needed = cmd_size;
	else
		cmd_needed = cmd_size + head_to_end(cmd_head, udev->cmdr_size);

	space = spc_free(cmd_head, udev->cmdr_last_cleaned, udev->cmdr_size);
	if (space < cmd_needed) {
		pr_debug("no cmd space: %u %u %u\n", cmd_head,
		       udev->cmdr_last_cleaned, udev->cmdr_size);
		return false;
	}

	/* try to check and get the data blocks as needed */
	space = spc_bitmap_free(udev->data_bitmap, udev->dbi_thresh);
	if ((space * DATA_BLOCK_SIZE) < data_needed) {
		unsigned long blocks_left =
				(udev->max_blocks - udev->dbi_thresh) + space;

		if (blocks_left < blocks_needed) {
			pr_debug("no data space: only %lu available, but ask for %zu\n",
					blocks_left * DATA_BLOCK_SIZE,
					data_needed);
			return false;
		}

		udev->dbi_thresh += blocks_needed;
		if (udev->dbi_thresh > udev->max_blocks)
			udev->dbi_thresh = udev->max_blocks;
	}

	return tcmu_get_empty_blocks(udev, cmd);
}

static inline size_t tcmu_cmd_get_base_cmd_size(size_t iov_cnt)
{
	return max(offsetof(struct tcmu_cmd_entry, req.iov[iov_cnt]),
			sizeof(struct tcmu_cmd_entry));
}

static inline size_t tcmu_cmd_get_cmd_size(struct tcmu_cmd *tcmu_cmd,
					   size_t base_command_size)
{
	struct se_cmd *se_cmd = tcmu_cmd->se_cmd;
	size_t command_size;

	command_size = base_command_size +
		round_up(scsi_command_size(se_cmd->t_task_cdb),
				TCMU_OP_ALIGN_SIZE);

	WARN_ON(command_size & (TCMU_OP_ALIGN_SIZE-1));

	return command_size;
}

static int tcmu_setup_cmd_timer(struct tcmu_cmd *tcmu_cmd, unsigned int tmo,
				struct timer_list *timer)
{
	struct tcmu_dev *udev = tcmu_cmd->tcmu_dev;
	int cmd_id;

	if (tcmu_cmd->cmd_id)
		goto setup_timer;

	cmd_id = idr_alloc(&udev->commands, tcmu_cmd, 1, USHRT_MAX, GFP_NOWAIT);
	if (cmd_id < 0) {
		pr_err("tcmu: Could not allocate cmd id.\n");
		return cmd_id;
	}
	tcmu_cmd->cmd_id = cmd_id;

	pr_debug("allocated cmd %u for dev %s tmo %lu\n", tcmu_cmd->cmd_id,
		 udev->name, tmo / MSEC_PER_SEC);

setup_timer:
	if (!tmo)
		return 0;

	tcmu_cmd->deadline = round_jiffies_up(jiffies + msecs_to_jiffies(tmo));
	mod_timer(timer, tcmu_cmd->deadline);
	return 0;
}

static int add_to_cmdr_queue(struct tcmu_cmd *tcmu_cmd)
{
	struct tcmu_dev *udev = tcmu_cmd->tcmu_dev;
	unsigned int tmo;
	int ret;

	/*
	 * For backwards compat if qfull_time_out is not set use
	 * cmd_time_out and if that's not set use the default time out.
	 */
	if (!udev->qfull_time_out)
		return -ETIMEDOUT;
	else if (udev->qfull_time_out > 0)
		tmo = udev->qfull_time_out;
	else if (udev->cmd_time_out)
		tmo = udev->cmd_time_out;
	else
		tmo = TCMU_TIME_OUT;

	ret = tcmu_setup_cmd_timer(tcmu_cmd, tmo, &udev->qfull_timer);
	if (ret)
		return ret;

	list_add_tail(&tcmu_cmd->cmdr_queue_entry, &udev->cmdr_queue);
	pr_debug("adding cmd %u on dev %s to ring space wait queue\n",
		 tcmu_cmd->cmd_id, udev->name);
	return 0;
}

/**
 * queue_cmd_ring - queue cmd to ring or internally
 * @tcmu_cmd: cmd to queue
 * @scsi_err: TCM error code if failure (-1) returned.
 *
 * Returns:
 * -1 we cannot queue internally or to the ring.
 *  0 success
 *  1 internally queued to wait for ring memory to free.
 */
static sense_reason_t queue_cmd_ring(struct tcmu_cmd *tcmu_cmd, int *scsi_err)
{
	struct tcmu_dev *udev = tcmu_cmd->tcmu_dev;
	struct se_cmd *se_cmd = tcmu_cmd->se_cmd;
	size_t base_command_size, command_size;
	struct tcmu_mailbox *mb;
	struct tcmu_cmd_entry *entry;
	struct iovec *iov;
	int iov_cnt, ret;
	uint32_t cmd_head;
	uint64_t cdb_off;
	bool copy_to_data_area;
	size_t data_length = tcmu_cmd_get_data_length(tcmu_cmd);

	*scsi_err = TCM_NO_SENSE;

	if (test_bit(TCMU_DEV_BIT_BLOCKED, &udev->flags)) {
		*scsi_err = TCM_LUN_BUSY;
		return -1;
	}

	if (test_bit(TCMU_DEV_BIT_BROKEN, &udev->flags)) {
		*scsi_err = TCM_LOGICAL_UNIT_COMMUNICATION_FAILURE;
		return -1;
	}

	/*
	 * Must be a certain minimum size for response sense info, but
	 * also may be larger if the iov array is large.
	 *
	 * We prepare as many iovs as possbile for potential uses here,
	 * because it's expensive to tell how many regions are freed in
	 * the bitmap & global data pool, as the size calculated here
	 * will only be used to do the checks.
	 *
	 * The size will be recalculated later as actually needed to save
	 * cmd area memories.
	 */
	base_command_size = tcmu_cmd_get_base_cmd_size(tcmu_cmd->dbi_cnt);
	command_size = tcmu_cmd_get_cmd_size(tcmu_cmd, base_command_size);

	if (!list_empty(&udev->cmdr_queue))
		goto queue;

	mb = udev->mb_addr;
	cmd_head = mb->cmd_head % udev->cmdr_size; /* UAM */
	if ((command_size > (udev->cmdr_size / 2)) ||
	    data_length > udev->data_size) {
		pr_warn("TCMU: Request of size %zu/%zu is too big for %u/%zu "
			"cmd ring/data area\n", command_size, data_length,
			udev->cmdr_size, udev->data_size);
		*scsi_err = TCM_INVALID_CDB_FIELD;
		return -1;
	}

	if (!is_ring_space_avail(udev, tcmu_cmd, command_size, data_length)) {
		/*
		 * Don't leave commands partially setup because the unmap
		 * thread might need the blocks to make forward progress.
		 */
		tcmu_cmd_free_data(tcmu_cmd, tcmu_cmd->dbi_cur);
		tcmu_cmd_reset_dbi_cur(tcmu_cmd);
		goto queue;
	}

	/* Insert a PAD if end-of-ring space is too small */
	if (head_to_end(cmd_head, udev->cmdr_size) < command_size) {
		size_t pad_size = head_to_end(cmd_head, udev->cmdr_size);

		entry = (void *) mb + CMDR_OFF + cmd_head;
		tcmu_hdr_set_op(&entry->hdr.len_op, TCMU_OP_PAD);
		tcmu_hdr_set_len(&entry->hdr.len_op, pad_size);
		entry->hdr.cmd_id = 0; /* not used for PAD */
		entry->hdr.kflags = 0;
		entry->hdr.uflags = 0;
		tcmu_flush_dcache_range(entry, sizeof(*entry));

		UPDATE_HEAD(mb->cmd_head, pad_size, udev->cmdr_size);
		tcmu_flush_dcache_range(mb, sizeof(*mb));

		cmd_head = mb->cmd_head % udev->cmdr_size; /* UAM */
		WARN_ON(cmd_head != 0);
	}

	entry = (void *) mb + CMDR_OFF + cmd_head;
	memset(entry, 0, command_size);
	tcmu_hdr_set_op(&entry->hdr.len_op, TCMU_OP_CMD);

	/* Handle allocating space from the data area */
	tcmu_cmd_reset_dbi_cur(tcmu_cmd);
	iov = &entry->req.iov[0];
	iov_cnt = 0;
	copy_to_data_area = (se_cmd->data_direction == DMA_TO_DEVICE
		|| se_cmd->se_cmd_flags & SCF_BIDI);
	scatter_data_area(udev, tcmu_cmd, se_cmd->t_data_sg,
			  se_cmd->t_data_nents, &iov, &iov_cnt,
			  copy_to_data_area);
	entry->req.iov_cnt = iov_cnt;

	/* Handle BIDI commands */
	iov_cnt = 0;
	if (se_cmd->se_cmd_flags & SCF_BIDI) {
		iov++;
		scatter_data_area(udev, tcmu_cmd, se_cmd->t_bidi_data_sg,
				  se_cmd->t_bidi_data_nents, &iov, &iov_cnt,
				  false);
	}
	entry->req.iov_bidi_cnt = iov_cnt;

	ret = tcmu_setup_cmd_timer(tcmu_cmd, udev->cmd_time_out,
				   &udev->cmd_timer);
	if (ret) {
		tcmu_cmd_free_data(tcmu_cmd, tcmu_cmd->dbi_cnt);
		mutex_unlock(&udev->cmdr_lock);

		*scsi_err = TCM_OUT_OF_RESOURCES;
		return -1;
	}
	entry->hdr.cmd_id = tcmu_cmd->cmd_id;

	/*
	 * Recalaulate the command's base size and size according
	 * to the actual needs
	 */
	base_command_size = tcmu_cmd_get_base_cmd_size(entry->req.iov_cnt +
						       entry->req.iov_bidi_cnt);
	command_size = tcmu_cmd_get_cmd_size(tcmu_cmd, base_command_size);

	tcmu_hdr_set_len(&entry->hdr.len_op, command_size);

	/* All offsets relative to mb_addr, not start of entry! */
	cdb_off = CMDR_OFF + cmd_head + base_command_size;
	memcpy((void *) mb + cdb_off, se_cmd->t_task_cdb, scsi_command_size(se_cmd->t_task_cdb));
	entry->req.cdb_off = cdb_off;
	tcmu_flush_dcache_range(entry, sizeof(*entry));

	UPDATE_HEAD(mb->cmd_head, command_size, udev->cmdr_size);
	tcmu_flush_dcache_range(mb, sizeof(*mb));

	/* TODO: only if FLUSH and FUA? */
	uio_event_notify(&udev->uio_info);

	return 0;

queue:
	if (add_to_cmdr_queue(tcmu_cmd)) {
		*scsi_err = TCM_OUT_OF_RESOURCES;
		return -1;
	}

	return 1;
}

static sense_reason_t
tcmu_queue_cmd(struct se_cmd *se_cmd)
{
	struct se_device *se_dev = se_cmd->se_dev;
	struct tcmu_dev *udev = TCMU_DEV(se_dev);
	struct tcmu_cmd *tcmu_cmd;
	sense_reason_t scsi_ret;
	int ret;

	tcmu_cmd = tcmu_alloc_cmd(se_cmd);
	if (!tcmu_cmd)
		return TCM_LOGICAL_UNIT_COMMUNICATION_FAILURE;

	mutex_lock(&udev->cmdr_lock);
	ret = queue_cmd_ring(tcmu_cmd, &scsi_ret);
	mutex_unlock(&udev->cmdr_lock);
	if (ret < 0)
		tcmu_free_cmd(tcmu_cmd);
	return scsi_ret;
}

static void tcmu_handle_completion(struct tcmu_cmd *cmd, struct tcmu_cmd_entry *entry)
{
	struct se_cmd *se_cmd = cmd->se_cmd;
	struct tcmu_dev *udev = cmd->tcmu_dev;

	/*
	 * cmd has been completed already from timeout, just reclaim
	 * data area space and free cmd
	 */
	if (test_bit(TCMU_CMD_BIT_EXPIRED, &cmd->flags))
		goto out;

	tcmu_cmd_reset_dbi_cur(cmd);

	if (entry->hdr.uflags & TCMU_UFLAG_UNKNOWN_OP) {
		pr_warn("TCMU: Userspace set UNKNOWN_OP flag on se_cmd %p\n",
			cmd->se_cmd);
		entry->rsp.scsi_status = SAM_STAT_CHECK_CONDITION;
	} else if (entry->rsp.scsi_status == SAM_STAT_CHECK_CONDITION) {
		transport_copy_sense_to_cmd(se_cmd, entry->rsp.sense_buffer);
	} else if (se_cmd->se_cmd_flags & SCF_BIDI) {
		/* Get Data-In buffer before clean up */
		gather_data_area(udev, cmd, true);
	} else if (se_cmd->data_direction == DMA_FROM_DEVICE) {
		gather_data_area(udev, cmd, false);
	} else if (se_cmd->data_direction == DMA_TO_DEVICE) {
		/* TODO: */
	} else if (se_cmd->data_direction != DMA_NONE) {
		pr_warn("TCMU: data direction was %d!\n",
			se_cmd->data_direction);
	}

	target_complete_cmd(cmd->se_cmd, entry->rsp.scsi_status);

out:
	cmd->se_cmd = NULL;
	tcmu_cmd_free_data(cmd, cmd->dbi_cnt);
	tcmu_free_cmd(cmd);
}

static unsigned int tcmu_handle_completions(struct tcmu_dev *udev)
{
	struct tcmu_mailbox *mb;
	int handled = 0;

	if (test_bit(TCMU_DEV_BIT_BROKEN, &udev->flags)) {
		pr_err("ring broken, not handling completions\n");
		return 0;
	}

	mb = udev->mb_addr;
	tcmu_flush_dcache_range(mb, sizeof(*mb));

	while (udev->cmdr_last_cleaned != READ_ONCE(mb->cmd_tail)) {

		struct tcmu_cmd_entry *entry = (void *) mb + CMDR_OFF + udev->cmdr_last_cleaned;
		struct tcmu_cmd *cmd;

		tcmu_flush_dcache_range(entry, sizeof(*entry));

		if (tcmu_hdr_get_op(entry->hdr.len_op) == TCMU_OP_PAD) {
			UPDATE_HEAD(udev->cmdr_last_cleaned,
				    tcmu_hdr_get_len(entry->hdr.len_op),
				    udev->cmdr_size);
			continue;
		}
		WARN_ON(tcmu_hdr_get_op(entry->hdr.len_op) != TCMU_OP_CMD);

		cmd = idr_remove(&udev->commands, entry->hdr.cmd_id);
		if (!cmd) {
			pr_err("cmd_id %u not found, ring is broken\n",
			       entry->hdr.cmd_id);
			set_bit(TCMU_DEV_BIT_BROKEN, &udev->flags);
			break;
		}

		tcmu_handle_completion(cmd, entry);

		UPDATE_HEAD(udev->cmdr_last_cleaned,
			    tcmu_hdr_get_len(entry->hdr.len_op),
			    udev->cmdr_size);

		handled++;
	}

	if (mb->cmd_tail == mb->cmd_head) {
		/* no more pending commands */
		del_timer(&udev->cmd_timer);

		if (list_empty(&udev->cmdr_queue)) {
			/*
			 * no more pending or waiting commands so try to
			 * reclaim blocks if needed.
			 */
			if (atomic_read(&global_db_count) >
			    tcmu_global_max_blocks)
				schedule_delayed_work(&tcmu_unmap_work, 0);
		}
	}

	return handled;
}

static int tcmu_check_expired_cmd(int id, void *p, void *data)
{
	struct tcmu_cmd *cmd = p;
	struct tcmu_dev *udev = cmd->tcmu_dev;
	u8 scsi_status;
	struct se_cmd *se_cmd;
	bool is_running;

	if (test_bit(TCMU_CMD_BIT_EXPIRED, &cmd->flags))
		return 0;

	if (!time_after(jiffies, cmd->deadline))
		return 0;

	is_running = list_empty(&cmd->cmdr_queue_entry);
	se_cmd = cmd->se_cmd;

	if (is_running) {
		/*
		 * If cmd_time_out is disabled but qfull is set deadline
		 * will only reflect the qfull timeout. Ignore it.
		 */
		if (!udev->cmd_time_out)
			return 0;

		set_bit(TCMU_CMD_BIT_EXPIRED, &cmd->flags);
		/*
		 * target_complete_cmd will translate this to LUN COMM FAILURE
		 */
		scsi_status = SAM_STAT_CHECK_CONDITION;
	} else {
		list_del_init(&cmd->cmdr_queue_entry);

		idr_remove(&udev->commands, id);
		tcmu_free_cmd(cmd);
		scsi_status = SAM_STAT_TASK_SET_FULL;
	}

	pr_debug("Timing out cmd %u on dev %s that is %s.\n",
		 id, udev->name, is_running ? "inflight" : "queued");

	target_complete_cmd(se_cmd, scsi_status);
	return 0;
}

static void tcmu_device_timedout(struct tcmu_dev *udev)
{
	spin_lock(&timed_out_udevs_lock);
	if (list_empty(&udev->timedout_entry))
		list_add_tail(&udev->timedout_entry, &timed_out_udevs);
	spin_unlock(&timed_out_udevs_lock);

	schedule_delayed_work(&tcmu_unmap_work, 0);
}

static void tcmu_cmd_timedout(struct timer_list *t)
{
	struct tcmu_dev *udev = from_timer(udev, t, cmd_timer);

	pr_debug("%s cmd timeout has expired\n", udev->name);
	tcmu_device_timedout(udev);
}

static void tcmu_qfull_timedout(struct timer_list *t)
{
	struct tcmu_dev *udev = from_timer(udev, t, qfull_timer);

	pr_debug("%s qfull timeout has expired\n", udev->name);
	tcmu_device_timedout(udev);
}

static int tcmu_attach_hba(struct se_hba *hba, u32 host_id)
{
	struct tcmu_hba *tcmu_hba;

	tcmu_hba = kzalloc(sizeof(struct tcmu_hba), GFP_KERNEL);
	if (!tcmu_hba)
		return -ENOMEM;

	tcmu_hba->host_id = host_id;
	hba->hba_ptr = tcmu_hba;

	return 0;
}

static void tcmu_detach_hba(struct se_hba *hba)
{
	kfree(hba->hba_ptr);
	hba->hba_ptr = NULL;
}

static struct se_device *tcmu_alloc_device(struct se_hba *hba, const char *name)
{
	struct tcmu_dev *udev;

	udev = kzalloc(sizeof(struct tcmu_dev), GFP_KERNEL);
	if (!udev)
		return NULL;
	kref_init(&udev->kref);

	udev->name = kstrdup(name, GFP_KERNEL);
	if (!udev->name) {
		kfree(udev);
		return NULL;
	}

	udev->hba = hba;
	udev->cmd_time_out = TCMU_TIME_OUT;
	udev->qfull_time_out = -1;

	udev->max_blocks = DATA_BLOCK_BITS_DEF;
	mutex_init(&udev->cmdr_lock);

	INIT_LIST_HEAD(&udev->timedout_entry);
	INIT_LIST_HEAD(&udev->cmdr_queue);
	idr_init(&udev->commands);

	timer_setup(&udev->qfull_timer, tcmu_qfull_timedout, 0);
	timer_setup(&udev->cmd_timer, tcmu_cmd_timedout, 0);

	init_waitqueue_head(&udev->nl_cmd_wq);
	spin_lock_init(&udev->nl_cmd_lock);

	INIT_RADIX_TREE(&udev->data_blocks, GFP_KERNEL);

	return &udev->se_dev;
}

static bool run_cmdr_queue(struct tcmu_dev *udev, bool fail)
{
	struct tcmu_cmd *tcmu_cmd, *tmp_cmd;
	LIST_HEAD(cmds);
	bool drained = true;
	sense_reason_t scsi_ret;
	int ret;

	if (list_empty(&udev->cmdr_queue))
		return true;

	pr_debug("running %s's cmdr queue forcefail %d\n", udev->name, fail);

	list_splice_init(&udev->cmdr_queue, &cmds);

	list_for_each_entry_safe(tcmu_cmd, tmp_cmd, &cmds, cmdr_queue_entry) {
		list_del_init(&tcmu_cmd->cmdr_queue_entry);

	        pr_debug("removing cmd %u on dev %s from queue\n",
		         tcmu_cmd->cmd_id, udev->name);

		if (fail) {
			idr_remove(&udev->commands, tcmu_cmd->cmd_id);
			/*
			 * We were not able to even start the command, so
			 * fail with busy to allow a retry in case runner
			 * was only temporarily down. If the device is being
			 * removed then LIO core will do the right thing and
			 * fail the retry.
			 */
			target_complete_cmd(tcmu_cmd->se_cmd, SAM_STAT_BUSY);
			tcmu_free_cmd(tcmu_cmd);
			continue;
		}

		ret = queue_cmd_ring(tcmu_cmd, &scsi_ret);
		if (ret < 0) {
		        pr_debug("cmd %u on dev %s failed with %u\n",
			         tcmu_cmd->cmd_id, udev->name, scsi_ret);

			idr_remove(&udev->commands, tcmu_cmd->cmd_id);
			/*
			 * Ignore scsi_ret for now. target_complete_cmd
			 * drops it.
			 */
			target_complete_cmd(tcmu_cmd->se_cmd,
					    SAM_STAT_CHECK_CONDITION);
			tcmu_free_cmd(tcmu_cmd);
		} else if (ret > 0) {
			pr_debug("ran out of space during cmdr queue run\n");
			/*
			 * cmd was requeued, so just put all cmds back in
			 * the queue
			 */
			list_splice_tail(&cmds, &udev->cmdr_queue);
			drained = false;
			goto done;
		}
	}
	if (list_empty(&udev->cmdr_queue))
		del_timer(&udev->qfull_timer);
done:
	return drained;
}

static int tcmu_irqcontrol(struct uio_info *info, s32 irq_on)
{
	struct tcmu_dev *udev = container_of(info, struct tcmu_dev, uio_info);

	mutex_lock(&udev->cmdr_lock);
	tcmu_handle_completions(udev);
	run_cmdr_queue(udev, false);
	mutex_unlock(&udev->cmdr_lock);

	return 0;
}

/*
 * mmap code from uio.c. Copied here because we want to hook mmap()
 * and this stuff must come along.
 */
static int tcmu_find_mem_index(struct vm_area_struct *vma)
{
	struct tcmu_dev *udev = vma->vm_private_data;
	struct uio_info *info = &udev->uio_info;

	if (vma->vm_pgoff < MAX_UIO_MAPS) {
		if (info->mem[vma->vm_pgoff].size == 0)
			return -1;
		return (int)vma->vm_pgoff;
	}
	return -1;
}

static struct page *tcmu_try_get_block_page(struct tcmu_dev *udev, uint32_t dbi)
{
	struct page *page;

	mutex_lock(&udev->cmdr_lock);
	page = tcmu_get_block_page(udev, dbi);
	if (likely(page)) {
		mutex_unlock(&udev->cmdr_lock);
		return page;
	}

	/*
	 * Userspace messed up and passed in a address not in the
	 * data iov passed to it.
	 */
	pr_err("Invalid addr to data block mapping  (dbi %u) on device %s\n",
	       dbi, udev->name);
	page = NULL;
	mutex_unlock(&udev->cmdr_lock);

	return page;
}

static int tcmu_vma_fault(struct vm_fault *vmf)
{
	struct tcmu_dev *udev = vmf->vma->vm_private_data;
	struct uio_info *info = &udev->uio_info;
	struct page *page;
	unsigned long offset;
	void *addr;

	int mi = tcmu_find_mem_index(vmf->vma);
	if (mi < 0)
		return VM_FAULT_SIGBUS;

	/*
	 * We need to subtract mi because userspace uses offset = N*PAGE_SIZE
	 * to use mem[N].
	 */
	offset = (vmf->pgoff - mi) << PAGE_SHIFT;

	if (offset < udev->data_off) {
		/* For the vmalloc()ed cmd area pages */
		addr = (void *)(unsigned long)info->mem[mi].addr + offset;
		page = vmalloc_to_page(addr);
	} else {
		uint32_t dbi;

		/* For the dynamically growing data area pages */
		dbi = (offset - udev->data_off) / DATA_BLOCK_SIZE;
		page = tcmu_try_get_block_page(udev, dbi);
		if (!page)
			return VM_FAULT_SIGBUS;
	}

	get_page(page);
	vmf->page = page;
	return 0;
}

static const struct vm_operations_struct tcmu_vm_ops = {
	.fault = tcmu_vma_fault,
};

static int tcmu_mmap(struct uio_info *info, struct vm_area_struct *vma)
{
	struct tcmu_dev *udev = container_of(info, struct tcmu_dev, uio_info);

	vma->vm_flags |= VM_DONTEXPAND | VM_DONTDUMP;
	vma->vm_ops = &tcmu_vm_ops;

	vma->vm_private_data = udev;

	/* Ensure the mmap is exactly the right size */
	if (vma_pages(vma) != (udev->ring_size >> PAGE_SHIFT))
		return -EINVAL;

	return 0;
}

static int tcmu_open(struct uio_info *info, struct inode *inode)
{
	struct tcmu_dev *udev = container_of(info, struct tcmu_dev, uio_info);

	/* O_EXCL not supported for char devs, so fake it? */
	if (test_and_set_bit(TCMU_DEV_BIT_OPEN, &udev->flags))
		return -EBUSY;

	udev->inode = inode;
	kref_get(&udev->kref);

	pr_debug("open\n");

	return 0;
}

static void tcmu_dev_call_rcu(struct rcu_head *p)
{
	struct se_device *dev = container_of(p, struct se_device, rcu_head);
	struct tcmu_dev *udev = TCMU_DEV(dev);

	kfree(udev->uio_info.name);
	kfree(udev->name);
	kfree(udev);
}

static int tcmu_check_and_free_pending_cmd(struct tcmu_cmd *cmd)
{
	if (test_bit(TCMU_CMD_BIT_EXPIRED, &cmd->flags)) {
		kmem_cache_free(tcmu_cmd_cache, cmd);
		return 0;
	}
	return -EINVAL;
}

static void tcmu_blocks_release(struct radix_tree_root *blocks,
				int start, int end)
{
	int i;
	struct page *page;

	for (i = start; i < end; i++) {
		page = radix_tree_delete(blocks, i);
		if (page) {
			__free_page(page);
			atomic_dec(&global_db_count);
		}
	}
}

static void tcmu_dev_kref_release(struct kref *kref)
{
	struct tcmu_dev *udev = container_of(kref, struct tcmu_dev, kref);
	struct se_device *dev = &udev->se_dev;
	struct tcmu_cmd *cmd;
	bool all_expired = true;
	int i;

	vfree(udev->mb_addr);
	udev->mb_addr = NULL;

	spin_lock_bh(&timed_out_udevs_lock);
	if (!list_empty(&udev->timedout_entry))
		list_del(&udev->timedout_entry);
	spin_unlock_bh(&timed_out_udevs_lock);

	/* Upper layer should drain all requests before calling this */
	mutex_lock(&udev->cmdr_lock);
	idr_for_each_entry(&udev->commands, cmd, i) {
		if (tcmu_check_and_free_pending_cmd(cmd) != 0)
			all_expired = false;
	}
	idr_destroy(&udev->commands);
	WARN_ON(!all_expired);

	tcmu_blocks_release(&udev->data_blocks, 0, udev->dbi_max + 1);
	kfree(udev->data_bitmap);
	mutex_unlock(&udev->cmdr_lock);

	call_rcu(&dev->rcu_head, tcmu_dev_call_rcu);
}

static int tcmu_release(struct uio_info *info, struct inode *inode)
{
	struct tcmu_dev *udev = container_of(info, struct tcmu_dev, uio_info);

	clear_bit(TCMU_DEV_BIT_OPEN, &udev->flags);

	pr_debug("close\n");
	/* release ref from open */
	kref_put(&udev->kref, tcmu_dev_kref_release);
	return 0;
}

static void tcmu_init_genl_cmd_reply(struct tcmu_dev *udev, int cmd)
{
	struct tcmu_nl_cmd *nl_cmd = &udev->curr_nl_cmd;

	if (!tcmu_kern_cmd_reply_supported)
		return;

	if (udev->nl_reply_supported <= 0)
		return;

relock:
	spin_lock(&udev->nl_cmd_lock);

	if (nl_cmd->cmd != TCMU_CMD_UNSPEC) {
		spin_unlock(&udev->nl_cmd_lock);
		pr_debug("sleeping for open nl cmd\n");
		wait_event(udev->nl_cmd_wq, (nl_cmd->cmd == TCMU_CMD_UNSPEC));
		goto relock;
	}

	memset(nl_cmd, 0, sizeof(*nl_cmd));
	nl_cmd->cmd = cmd;
	init_completion(&nl_cmd->complete);

	spin_unlock(&udev->nl_cmd_lock);
}

static int tcmu_wait_genl_cmd_reply(struct tcmu_dev *udev)
{
	struct tcmu_nl_cmd *nl_cmd = &udev->curr_nl_cmd;
	int ret;
	DEFINE_WAIT(__wait);

	if (!tcmu_kern_cmd_reply_supported)
		return 0;

	if (udev->nl_reply_supported <= 0)
		return 0;

	pr_debug("sleeping for nl reply\n");
	wait_for_completion(&nl_cmd->complete);

	spin_lock(&udev->nl_cmd_lock);
	nl_cmd->cmd = TCMU_CMD_UNSPEC;
	ret = nl_cmd->status;
	nl_cmd->status = 0;
	spin_unlock(&udev->nl_cmd_lock);

	wake_up_all(&udev->nl_cmd_wq);

	return ret;
}

static int tcmu_netlink_event_init(struct tcmu_dev *udev,
				   enum tcmu_genl_cmd cmd,
				   struct sk_buff **buf, void **hdr)
{
	struct sk_buff *skb;
	void *msg_header;
	int ret = -ENOMEM;

	skb = genlmsg_new(NLMSG_GOODSIZE, GFP_KERNEL);
	if (!skb)
		return ret;

	msg_header = genlmsg_put(skb, 0, 0, &tcmu_genl_family, 0, cmd);
	if (!msg_header)
		goto free_skb;

	ret = nla_put_string(skb, TCMU_ATTR_DEVICE, udev->uio_info.name);
	if (ret < 0)
		goto free_skb;

	ret = nla_put_u32(skb, TCMU_ATTR_MINOR, udev->uio_info.uio_dev->minor);
	if (ret < 0)
		goto free_skb;

	ret = nla_put_u32(skb, TCMU_ATTR_DEVICE_ID, udev->se_dev.dev_index);
	if (ret < 0)
		goto free_skb;

	*buf = skb;
	*hdr = msg_header;
	return ret;

free_skb:
	nlmsg_free(skb);
	return ret;
}

static int tcmu_netlink_event_send(struct tcmu_dev *udev,
				   enum tcmu_genl_cmd cmd,
				   struct sk_buff **buf, void **hdr)
{
	int ret = 0;
	struct sk_buff *skb = *buf;
	void *msg_header = *hdr;

	genlmsg_end(skb, msg_header);

	tcmu_init_genl_cmd_reply(udev, cmd);

	ret = genlmsg_multicast_allns(&tcmu_genl_family, skb, 0,
				      TCMU_MCGRP_CONFIG, GFP_KERNEL);
       /* We don't care if no one is listening */
	if (ret == -ESRCH)
		ret = 0;
	if (!ret)
		ret = tcmu_wait_genl_cmd_reply(udev);
	return ret;
}

static int tcmu_send_dev_add_event(struct tcmu_dev *udev)
{
	struct sk_buff *skb = NULL;
	void *msg_header = NULL;
	int ret = 0;

	ret = tcmu_netlink_event_init(udev, TCMU_CMD_ADDED_DEVICE, &skb,
				      &msg_header);
	if (ret < 0)
		return ret;
	return tcmu_netlink_event_send(udev, TCMU_CMD_ADDED_DEVICE, &skb,
				       &msg_header);

}

static int tcmu_send_dev_remove_event(struct tcmu_dev *udev)
{
	struct sk_buff *skb = NULL;
	void *msg_header = NULL;
	int ret = 0;

	ret = tcmu_netlink_event_init(udev, TCMU_CMD_REMOVED_DEVICE,
				      &skb, &msg_header);
	if (ret < 0)
		return ret;
	return tcmu_netlink_event_send(udev, TCMU_CMD_REMOVED_DEVICE,
				       &skb, &msg_header);
}

static int tcmu_send_get_pr_info_event(struct tcmu_dev *udev)
{
	struct sk_buff *skb = NULL;
	void *msg_header = NULL;
	int ret = 0;

	ret = tcmu_netlink_event_init(udev, TCMU_CMD_GET_PR_INFO,
				      &skb, &msg_header);
	if (ret < 0)
		return ret;

	return tcmu_netlink_event_send(udev, TCMU_CMD_GET_PR_INFO,
				       &skb, &msg_header);
}

static int tcmu_send_set_pr_info_event(struct tcmu_dev *udev, char *buf)
{
	struct sk_buff *skb = NULL;
	void *msg_header = NULL;
	int ret = 0;

	ret = tcmu_netlink_event_init(udev, TCMU_CMD_SET_PR_INFO,
				      &skb, &msg_header);
	if (ret < 0)
		return ret;
	ret = nla_put_string(skb, TCMU_ATTR_PR_INFO, buf);
	if (ret < 0) {
		nlmsg_free(skb);
		return ret;
	}

	return tcmu_netlink_event_send(udev, TCMU_CMD_SET_PR_INFO,
				       &skb, &msg_header);
}

static int tcmu_update_uio_info(struct tcmu_dev *udev)
{
	struct tcmu_hba *hba = udev->hba->hba_ptr;
	struct uio_info *info;
	size_t size, used;
	char *str;

	info = &udev->uio_info;
	size = snprintf(NULL, 0, "tcm-user/%u/%s/%s", hba->host_id, udev->name,
			udev->dev_config);
	size += 1; /* for \0 */
	str = kmalloc(size, GFP_KERNEL);
	if (!str)
		return -ENOMEM;

	used = snprintf(str, size, "tcm-user/%u/%s", hba->host_id, udev->name);
	if (udev->dev_config[0])
		snprintf(str + used, size - used, "/%s", udev->dev_config);

	/* If the old string exists, free it */
	kfree(info->name);
	info->name = str;

	return 0;
}

/*
 * This funtion will get PR INFO(a string)from a TCMU device.
 * PR INFO will be stored at udev->pr_info.pr_info_buf.
 */
static int tcmu_get_dev_pr_info(struct tcmu_dev *udev, int *val_len)
{
	int ret = 0;

	ret = tcmu_send_get_pr_info_event(udev);
	*val_len = strlen(udev->pr_info.pr_info_buf);
	if (*val_len == 0)
		ret = -ENODATA;

	return ret;
}

/*
 * This function will store PR INFO(a string) to a TCMU
 * device metadata.
 */
static int tcmu_set_dev_pr_info(struct tcmu_dev *udev, void *val)
{
	return tcmu_send_set_pr_info_event(udev, val);
}

static int
tcmu_gen_it_nexus(struct se_session *se_sess,
		     char *nexus_buf,
		     size_t buflen)
{
	struct se_portal_group *se_tpg;
	const struct target_core_fabric_ops *tfo;
	u32 tpg_tag = 0;
	char *tpg_wwn = "";
	int rc;

	if (!se_sess || !se_sess->se_node_acl || !se_sess->se_tpg
	    || !se_sess->se_tpg->se_tpg_tfo) {
		pr_warn("invalid session for IT nexus generation\n");
		return -EINVAL;
	}

	se_tpg = se_sess->se_tpg;
	tfo = se_tpg->se_tpg_tfo;

	/*
	 * nexus generation may be coming from an xcopy, in which case tfo
	 * refers to xcopy_pt_tfo (tpg_get_wwn and tpg_get_tag are NULL).
	 */
	if (tfo->tpg_get_tag)
		tpg_tag = tfo->tpg_get_tag(se_tpg);
	if (tfo->tpg_get_wwn)
		tpg_wwn = tfo->tpg_get_wwn(se_tpg);

	rc = snprintf(nexus_buf, buflen, "%s,i,0x%llx,%s,t,0x%x",
		      se_sess->se_node_acl->initiatorname,
		      se_sess->sess_bin_isid,
		      tpg_wwn,
		      tpg_tag);
	if ((rc < 0) || (rc >= buflen)) {
		pr_debug("error formatting reserve cookie\n");
		return -EINVAL;
	}

	pr_debug("generated nexus: %s\n", nexus_buf);

	return 0;
}

static int
tcmu_pr_info_seq_decode(char *str, u32 *seq)
{
	int rc;

	if (!seq) {
		WARN_ON(1);
		return -EINVAL;
	}
	rc = sscanf(str, "0x%08x", seq);
	if (rc != 1) {
		pr_err("failed to decode PR info seqnum in: %s\n", str);
		return -EINVAL;
	}

	pr_debug("processed pr_info seqnum: %u\n", *seq);

	return 0;
}

static int
tcmu_pr_info_vers_seq_encode(char *buf, size_t buf_remain, u32 vers, u32 seq)
{
	int rc;

	rc = snprintf(buf, buf_remain, "0x%08x\n0x%08x\n",
		      vers, seq);
	if ((rc < 0) || (rc >= buf_remain)) {
		pr_err("failed to encode PR vers and seq\n");
		return -EINVAL;
	}

	return rc;
}

static int
tcmu_pr_info_vers_decode(char *str, u32 *vers)
{
	int rc;

	if (!vers) {
		WARN_ON(1);
		return -EINVAL;
	}
	rc = sscanf(str, "0x%08x", vers);
	if (rc != 1) {
		pr_err("failed to decode PR info version in: %s\n", str);
		return -EINVAL;
	}

	if (*vers != TCMU_PR_INFO_XATTR_VERS) {
		pr_err("unsupported PR info version: %u\n", *vers);
		return -EINVAL;
	}

	pr_debug("processed pr_info version: %u\n", *vers);

	return 0;
}

static int
tcmu_pr_info_scsi2_rsv_decode(char *str, struct tcmu_scsi2_rsv **_scsi2_rsv)
{
	struct tcmu_scsi2_rsv *scsi2_rsv;

	if (!_scsi2_rsv) {
		WARN_ON(1);
		return -EINVAL;
	}
	if (!strncmp(str, TCMU_PR_INFO_XATTR_VAL_SCSI2_RSV_ABSENT,
		     sizeof(TCMU_PR_INFO_XATTR_VAL_SCSI2_RSV_ABSENT))) {
		scsi2_rsv = NULL;
	} else {
		size_t n;

		scsi2_rsv = kzalloc(sizeof(*scsi2_rsv), GFP_KERNEL);
		if (!scsi2_rsv)
			return -ENOMEM;

		n = strlcpy(scsi2_rsv->it_nexus, str,
			    TCMU_PR_IT_NEXUS_MAXLEN);
		if (n >= TCMU_PR_IT_NEXUS_MAXLEN) {
			kfree(scsi2_rsv);
			return -EINVAL;
		}
	}

	pr_debug("processed pr_info SCSI2 rsv: %s\n", str);

	*_scsi2_rsv = scsi2_rsv;
	return 0;
}

static int
tcmu_pr_info_scsi2_rsv_encode(char *buf, size_t buf_remain,
			      struct tcmu_scsi2_rsv *scsi2_rsv)
{
	int rc;

	if (!scsi2_rsv) {
		/* no reservation */
		rc = snprintf(buf, buf_remain, "%s\n",
			      TCMU_PR_INFO_XATTR_VAL_SCSI2_RSV_ABSENT);
	} else {
		rc = snprintf(buf, buf_remain, "%s\n", scsi2_rsv->it_nexus);
	}
	if ((rc < 0) || (rc >= buf_remain)) {
		pr_err("failed to encode SCSI2 reservation\n");
		return -EINVAL;
	}

	return rc;
}

static int
tcmu_pr_info_gen_decode(char *str, u32 *gen)
{
	int rc;

	if (!gen) {
		WARN_ON(1);
		return -EINVAL;
	}
	rc = sscanf(str, "0x%08x", gen);
	if (rc != 1) {
		pr_err("failed to parse PR gen: %s\n", str);
		return -EINVAL;
	}

	pr_debug("processed pr_info generation: %s\n", str);

	return 0;
}

static int
tcmu_pr_info_gen_encode(char *buf, size_t buf_remain, u32 gen)
{
	int rc;

	rc = snprintf(buf, buf_remain, "0x%08x\n", gen);
	if ((rc < 0) || (rc >= buf_remain)) {
		pr_err("failed to encode PR gen\n");
		return -EINVAL;
	}

	return rc;
}

static int tcmu_pr_info_rsv_decode(char *str, struct tcmu_pr_rsv **_rsv)
{
	struct tcmu_pr_rsv *rsv;
	int rc;

	if (!_rsv) {
		WARN_ON(1);
		return -EINVAL;
	}
	if (!strncmp(str, TCMU_PR_INFO_XATTR_VAL_SCSI3_RSV_ABSENT,
		     sizeof(TCMU_PR_INFO_XATTR_VAL_SCSI3_RSV_ABSENT))) {
		/* no reservation. Ensure pr_info->rsv is NULL */
		rsv = NULL;
	} else {
		rsv = kzalloc(sizeof(*rsv), GFP_KERNEL);
		if (!rsv)
			return -ENOMEM;

		/* reservation key, I-T nexus and type with space separators */
		rc = sscanf(str, "0x%016llx %"
			    __stringify(TCMU_PR_IT_NEXUS_MAXLEN)
			    "s 0x%08x", &rsv->key, rsv->it_nexus, &rsv->type);
		if (rc != 3) {
			pr_err("failed to parse PR rsv: %s\n", str);
			kfree(rsv);
			return -EINVAL;
		}
	}

	pr_debug("processed pr_info rsv: %s\n", str);
	*_rsv = rsv;
	return 0;
}

static int tcmu_pr_info_rsv_encode(char *buf, size_t buf_remain,
				   struct tcmu_pr_rsv *rsv)
{
	int rc;

	if (!rsv) {
		/* no reservation */
		rc = snprintf(buf, buf_remain, "%s\n",
			      TCMU_PR_INFO_XATTR_VAL_SCSI3_RSV_ABSENT);
	} else {
		rc = snprintf(buf, buf_remain, "0x%016llx %s 0x%08x\n",
			      rsv->key, rsv->it_nexus, rsv->type);
	}
	if ((rc < 0) || (rc >= buf_remain)) {
		pr_err("failed to encode PR reservation\n");
		return -EINVAL;
	}

	return rc;
}

static int
tcmu_pr_info_num_regs_decode(char *str, u32 *num_regs)
{
	int rc;

	if (!num_regs) {
		WARN_ON(1);
		return -EINVAL;
	}

	rc = sscanf(str, "0x%08x", num_regs);
	if (rc != 1) {
		pr_err("failed to parse PR num regs: %s\n", str);
		return -EINVAL;
	}
	pr_debug("processed pr_info num_regs: %s\n", str);

	return 0;
}

static int tcmu_pr_info_num_regs_encode(char *buf, size_t buf_remain,
					u32 num_regs)
{
	int rc;

	rc = snprintf(buf, buf_remain, "0x%08x\n", num_regs);
	if ((rc < 0) || (rc >= buf_remain)) {
		pr_err("failed to encode PR num_regs\n");
		return -EINVAL;
	}

	return rc;
}

static int tcmu_pr_info_reg_decode(char *str, struct tcmu_pr_reg **_reg)
{
	struct tcmu_pr_reg *reg;
	int rc;

	if (!_reg) {
		WARN_ON(1);
		return -EINVAL;
	}

	reg = kzalloc(sizeof(*reg), GFP_KERNEL);
	if (!reg)
		return -ENOMEM;

	/* registration key and I-T nexus with space separator */
	rc = sscanf(str, "0x%016llx %" __stringify(TCMU_PR_IT_NEXUS_MAXLEN)
			 "s", &reg->key, reg->it_nexus);
	if (rc != 2) {
		pr_err("failed to parse PR reg: %s\n", str);
		kfree(reg);
		return -EINVAL;
	}

	pr_debug("processed pr_info reg: %s\n", str);
	*_reg = reg;

	return 0;
}

static int tcmu_pr_info_reg_encode(char *buf, size_t buf_remain,
				   struct tcmu_pr_reg *reg)
{
	int rc;

	rc = snprintf(buf, buf_remain, "0x%016llx %s\n", reg->key,
		      reg->it_nexus);
	if ((rc < 0) || (rc >= buf_remain)) {
		pr_err("failed to encode PR registration\n");
		return -EINVAL;
	}

	return rc;
}

static void
tcmu_pr_info_free(struct tcmu_pr_info *pr_info)
{
	struct tcmu_pr_reg *reg;
	struct tcmu_pr_reg *reg_n;

	kfree(pr_info->scsi2_rsv);
	kfree(pr_info->rsv);
	list_for_each_entry_safe(reg, reg_n, &pr_info->regs, regs_node) {
		kfree(reg);
	}
	kfree(pr_info);
}

static int tcmu_pr_info_decode(char *pr_xattr, int pr_xattr_len,
			       struct tcmu_pr_info **_pr_info)
{
	struct tcmu_pr_info *pr_info;
	int rc;
	int field;
	int i;
	char *p;
	char *str;
	char *end;

	WARN_ON(!_pr_info);

	if (!pr_xattr_len) {
		pr_err("zero length PR xattr\n");
		return -EINVAL;
	}

	pr_debug("decoding PR xattr: %s\n", pr_xattr);

	pr_info = kzalloc(sizeof(*pr_info), GFP_KERNEL);
	if (!pr_info)
		return -ENOMEM;

	INIT_LIST_HEAD(&pr_info->regs);

	p = pr_xattr;
	end = pr_xattr + pr_xattr_len;
	field = 0;
	i = 0;
	/*
	 * '\n' separator between header fields and each reg entry.
	 * reg subfields are further separated by ' '.
	 */
	for (str = strsep(&p, "\n"); str && *str != '\0' && (p <= end);
	     str = strsep(&p, "\n")) {
		if (field == TCMU_PR_INFO_XATTR_FIELD_VER) {
			rc = tcmu_pr_info_vers_decode(str, &pr_info->vers);
			if (rc < 0)
				goto err_info_free;
		} else if (field == TCMU_PR_INFO_XATTR_FIELD_SEQ) {
			rc = tcmu_pr_info_seq_decode(str, &pr_info->seq);
			if (rc < 0)
				goto err_info_free;
		} else if (field == TCMU_PR_INFO_XATTR_FIELD_SCSI2_RSV) {
			rc = tcmu_pr_info_scsi2_rsv_decode(str,
							   &pr_info->scsi2_rsv);
			if (rc < 0)
				goto err_info_free;
		} else if (field == TCMU_PR_INFO_XATTR_FIELD_GEN) {
			rc = tcmu_pr_info_gen_decode(str, &pr_info->gen);
			if (rc < 0)
				goto err_info_free;
		} else if (field == TCMU_PR_INFO_XATTR_FIELD_SCSI3_RSV) {
			rc = tcmu_pr_info_rsv_decode(str, &pr_info->rsv);
			if (rc < 0)
				goto err_info_free;
		} else if (field == TCMU_PR_INFO_XATTR_FIELD_NUM_REGS) {
			rc = tcmu_pr_info_num_regs_decode(str,
							  &pr_info->num_regs);
			if (rc < 0)
				goto err_info_free;
		} else if (field >= TCMU_PR_INFO_XATTR_FIELD_REGS_START) {
			struct tcmu_pr_reg *reg;

			rc = tcmu_pr_info_reg_decode(str, &reg);
			if (rc < 0)
				goto err_info_free;
			list_add_tail(&reg->regs_node, &pr_info->regs);
			i++;
		} else {
			pr_debug("skipping parsing of field %d\n", field);
		}

		field++;
	}

	if (field <= TCMU_PR_INFO_XATTR_FIELD_NUM_REGS) {
		pr_err("pr_info missing basic fields, stopped at %d\n", field);
		rc = -EINVAL;
		goto err_info_free;
	}

	if (i != pr_info->num_regs) {
		pr_err("processed %d registrations, expected %d\n",
		       i, pr_info->num_regs);
		rc = -EINVAL;
		goto err_info_free;
	}

	pr_debug("successfully processed all PR data\n");
	*_pr_info = pr_info;

	return 0;

err_info_free:
	tcmu_pr_info_free(pr_info);
	return rc;
}

static int tcmu_pr_info_get(struct tcmu_dev *udev,
			    struct tcmu_pr_info **_pr_info,
			    char **_pr_xattr, int *_pr_xattr_len)
{
	int rc;
	char *pr_xattr = udev->pr_info.pr_info_buf;
	char *dup_xattr = NULL;
	int pr_xattr_len = 0;
	struct tcmu_pr_info *pr_info = NULL;

	if (!_pr_info) {
		WARN_ON(1);
		return -EINVAL;
	}

	rc = tcmu_get_dev_pr_info(udev, &pr_xattr_len);

	if (rc) {
		if (rc != -ENODATA)
			pr_err("failed to obtain PR xattr: %d\n", rc);
		return rc;
	}

	if (_pr_xattr) {
		/* dup before decode, which trashes @pr_xattr */
		dup_xattr = kstrdup(pr_xattr, GFP_KERNEL);
		if (!dup_xattr)
			return -ENOMEM;
	}

	rc = tcmu_pr_info_decode(pr_xattr, pr_xattr_len, &pr_info);
	if (rc) {
		pr_err("failed to decode PR xattr: %d\n", rc);
		goto err_dup_xattr_free;
	}

	if (_pr_xattr) {
		WARN_ON(!_pr_xattr_len);
		*_pr_xattr = dup_xattr;
		*_pr_xattr_len = pr_xattr_len;
	}

	*_pr_info = pr_info;
	pr_debug("successfully obtained PR info\n");
	return 0;

err_dup_xattr_free:
	kfree(dup_xattr);
	return rc;
}

static int tcmu_pr_info_encode(struct tcmu_pr_info *pr_info,
			       char **_pr_xattr, int *pr_xattr_len)
{
	struct tcmu_pr_reg *reg;
	char *pr_xattr;
	char *p;
	size_t buf_remain;
	int rc;
	int i;

	if (pr_info->vers != TCMU_PR_INFO_XATTR_VERS) {
		pr_err("unsupported PR info version: %u\n", pr_info->vers);
		return -EINVAL;
	}

	buf_remain = TCMU_PR_INFO_XATTR_ENCODED_MAXLEN(pr_info->num_regs);
	if (buf_remain > TCMU_PR_INFO_XATTR_MAX_SIZE) {
		pr_err("PR info too large for encoding: %zd\n", buf_remain);
		return -EINVAL;
	}
	pr_debug("encoding PR info: vers=%u, seq=%u, gen=%u, num regs=%u ",
	       pr_info->vers, pr_info->seq, pr_info->gen, pr_info->num_regs);
	pr_debug("into %zd bytes\n", buf_remain);

	pr_xattr = kmalloc(buf_remain, GFP_KERNEL);
	if (!pr_xattr)
		return -ENOMEM;

	p = pr_xattr;
	rc = tcmu_pr_info_vers_seq_encode(p, buf_remain, pr_info->vers,
					  pr_info->seq);
	if (rc < 0) {
		rc = -EINVAL;
		goto err_xattr_free;
	}

	p += rc;
	buf_remain -= rc;

	rc = tcmu_pr_info_scsi2_rsv_encode(p, buf_remain, pr_info->scsi2_rsv);
	if (rc < 0) {
		rc = -EINVAL;
		goto err_xattr_free;
	}

	p += rc;
	buf_remain -= rc;

	rc = tcmu_pr_info_gen_encode(p, buf_remain, pr_info->gen);
	if (rc < 0) {
		rc = -EINVAL;
		goto err_xattr_free;
	}

	p += rc;
	buf_remain -= rc;

	rc = tcmu_pr_info_rsv_encode(p, buf_remain, pr_info->rsv);
	if (rc < 0) {
		rc = -EINVAL;
		goto err_xattr_free;
	}

	p += rc;
	buf_remain -= rc;

	rc = tcmu_pr_info_num_regs_encode(p, buf_remain, pr_info->num_regs);
	if (rc < 0) {
		rc = -EINVAL;
		goto err_xattr_free;
	}

	p += rc;
	buf_remain -= rc;

	i = 0;
	list_for_each_entry(reg, &pr_info->regs, regs_node) {
		rc = tcmu_pr_info_reg_encode(p, buf_remain, reg);
		if (rc < 0) {
			rc = -EINVAL;
			goto err_xattr_free;
		}

		p += rc;
		buf_remain -= rc;
		i++;
	}

	if (i != pr_info->num_regs) {
		pr_err("mismatch between PR num_regs and list entries!\n");
		rc = -EINVAL;
		goto err_xattr_free;
	}

	*_pr_xattr = pr_xattr;
	/* +1 to include null term */
	*pr_xattr_len = (p - pr_xattr) + 1;

	pr_err("successfully encoded all %d PR regs into %d bytes: %s\n",
	       pr_info->num_regs, *pr_xattr_len, pr_xattr);

	return 0;

err_xattr_free:
	kfree(pr_xattr);
	return rc;
}

static int tcmu_pr_info_init(struct tcmu_dev *udev,
			     struct tcmu_pr_info **_pr_info,
			     char **_pr_xattr, int *_pr_xattr_len)
{
	struct tcmu_pr_info *pr_info;
	char *pr_xattr = NULL;
	int pr_xattr_len = 0;
	int rc;

	pr_info = kzalloc(sizeof(*pr_info), GFP_KERNEL);
	if (!pr_info)
		return -ENOMEM;

	pr_info->vers = TCMU_PR_INFO_XATTR_VERS;
	INIT_LIST_HEAD(&pr_info->regs);
	pr_info->seq = 1;

	rc = tcmu_pr_info_encode(pr_info, &pr_xattr, &pr_xattr_len);
	if (rc) {
		pr_err("failed to encode PR xattr: %d\n", rc);
		goto err_info_free;
	}

	rc = tcmu_set_dev_pr_info(udev, pr_xattr);
	if (rc) {
		pr_err("failed to set PR xattr: %d\n", rc);
		goto err_xattr_free;
	}

	*_pr_info = pr_info;
	if (_pr_xattr) {
		WARN_ON(!_pr_xattr_len);
		*_pr_xattr = pr_xattr;
		*_pr_xattr_len = pr_xattr_len;
	} else {
		kfree(pr_xattr);
	}
	pr_debug("successfully initialized PR info\n");

	return 0;

err_xattr_free:
	kfree(pr_xattr);
err_info_free:
	kfree(pr_info);
	return rc;
}

static int tcmu_pr_info_append_reg(struct tcmu_pr_info *pr_info,
				   char *nexus, u64 key)
{
	struct tcmu_pr_reg *reg;

	reg = kmalloc(sizeof(*reg), GFP_KERNEL);
	if (!reg)
		return -ENOMEM;

	reg->key = key;
	strlcpy(reg->it_nexus, nexus, ARRAY_SIZE(reg->it_nexus));

	list_add_tail(&reg->regs_node, &pr_info->regs);
	pr_info->num_regs++;

	pr_debug("appended pr_info reg: 0x%llx\n", reg->key);

	return 0;
}

/* handle PR registration for a currently unregistered I_T nexus */
static sense_reason_t
tcmu_execute_pr_register_new(struct tcmu_pr_info *pr_info, u64 old_key,
			     u64 new_key, char *it_nexus,
			     bool ignore_existing)
{
	sense_reason_t ret;
	int rc;

	pr_debug("PR registration for unregistered nexus: %s\n", it_nexus);
	if (!ignore_existing && (old_key != 0)) {
		ret = TCM_RESERVATION_CONFLICT;
		goto out;
	}
	if (new_key == 0) {
		ret = TCM_NO_SENSE;
		goto out;
	}
	/*
	 * Register the I_T nexus on which the command was received with
	 * the value specified in the SERVICE ACTION RESERVATION KEY
	 * field.
	 */
	rc = tcmu_pr_info_append_reg(pr_info, it_nexus, new_key);
	if (rc < 0) {
		ret = TCM_OUT_OF_RESOURCES;
		goto out;
	}

	ret = TCM_NO_SENSE;
out:
	return ret;
}

static bool tcmu_is_rsv_holder(struct tcmu_pr_rsv *rsv,
			       struct tcmu_pr_reg *reg, bool *rsv_is_all_reg)
{
	if (!rsv || !reg) {
		WARN_ON(1);
		return false;
	}
	if ((rsv->type == PR_TYPE_WRITE_EXCLUSIVE_ALLREG)
	    || (rsv->type == PR_TYPE_EXCLUSIVE_ACCESS_ALLREG)) {
		/* any registeration is a reservation holder */
		if (rsv_is_all_reg)
			*rsv_is_all_reg = true;
		return true;
	}

	if (rsv_is_all_reg)
		*rsv_is_all_reg = false;

	if ((rsv->key == reg->key)
	    && !strncmp(rsv->it_nexus, reg->it_nexus,
			ARRAY_SIZE(rsv->it_nexus))) {
		return true;
	}

	return false;
}

static void tcmu_pr_info_clear_reg(struct tcmu_pr_info *pr_info,
				   struct tcmu_pr_reg *reg)
{
	list_del(&reg->regs_node);
	pr_info->num_regs--;

	pr_debug("deleted pr_info reg: 0x%llx\n", reg->key);

	kfree(reg);
}

static void tcmu_pr_info_rsv_clear(struct tcmu_pr_info *pr_info)
{
	kfree(pr_info->rsv);
	pr_info->rsv = NULL;

	pr_debug("pr_info rsv cleared\n");
}

static int tcmu_pr_info_unregister_reg(struct tcmu_pr_info *pr_info,
				       struct tcmu_pr_reg *reg)
{
	struct tcmu_pr_rsv *rsv;
	bool all_reg = false;

	rsv = pr_info->rsv;
	if (rsv && tcmu_is_rsv_holder(rsv, reg, &all_reg)) {
		/*
		 * If the persistent reservation holder is more than one I_T
		 * nexus, the reservation shall not be released until the
		 * registrations for all persistent reservation holder I_T
		 * nexuses are removed.
		 */
		if (!all_reg || (pr_info->num_regs == 1)) {
			pr_warn("implicitly releasing PR of type %d",
				rsv->type);
			pr_warn("on unregister I_T Nexus %s\n",
				reg->it_nexus);
			tcmu_pr_info_rsv_clear(pr_info);
		}
	}

	tcmu_pr_info_clear_reg(pr_info, reg);

	return 0;
}

/* handle PR registration for a currently registered I_T nexus */
static sense_reason_t
tcmu_execute_pr_register_existing(struct tcmu_pr_info *pr_info,
				  u64 old_key, u64 new_key, char *it_nexus,
				  struct tcmu_pr_reg *existing_reg,
				  bool ignore_existing)
{
	sense_reason_t ret;
	int rc;

	pr_debug("PR registration for registered nexus: %s\n", it_nexus);

	if (!ignore_existing && (old_key != existing_reg->key)) {
		ret = TCM_RESERVATION_CONFLICT;
		goto out;
	}

	if (new_key == 0) {
		/* unregister */
		rc = tcmu_pr_info_unregister_reg(pr_info, existing_reg);
		if (rc < 0) {
			ret = TCM_OUT_OF_RESOURCES;
			goto out;
		}
	} else {
		/* update key */
		existing_reg->key = new_key;
	}

	ret = TCM_NO_SENSE;
out:
	return ret;
}

static int tcmu_configure_device(struct se_device *dev)
{
	struct tcmu_dev *udev = TCMU_DEV(dev);
	struct uio_info *info;
	struct tcmu_mailbox *mb;
	int ret = 0;

	ret = tcmu_update_uio_info(udev);
	if (ret)
		return ret;

	info = &udev->uio_info;

	udev->data_bitmap = kzalloc(BITS_TO_LONGS(udev->max_blocks) *
				    sizeof(unsigned long), GFP_KERNEL);
	if (!udev->data_bitmap) {
		ret = -ENOMEM;
		goto err_bitmap_alloc;
	}

	udev->mb_addr = vzalloc(CMDR_SIZE);
	if (!udev->mb_addr) {
		ret = -ENOMEM;
		goto err_vzalloc;
	}

	/* mailbox fits in first part of CMDR space */
	udev->cmdr_size = CMDR_SIZE - CMDR_OFF;
	udev->data_off = CMDR_SIZE;
	udev->data_size = udev->max_blocks * DATA_BLOCK_SIZE;
	udev->dbi_thresh = 0; /* Default in Idle state */

	/* Initialise the mailbox of the ring buffer */
	mb = udev->mb_addr;
	mb->version = TCMU_MAILBOX_VERSION;
	mb->flags = TCMU_MAILBOX_FLAG_CAP_OOOC;
	mb->cmdr_off = CMDR_OFF;
	mb->cmdr_size = udev->cmdr_size;

	WARN_ON(!PAGE_ALIGNED(udev->data_off));
	WARN_ON(udev->data_size % PAGE_SIZE);
	WARN_ON(udev->data_size % DATA_BLOCK_SIZE);

	info->version = __stringify(TCMU_MAILBOX_VERSION);

	info->mem[0].name = "tcm-user command & data buffer";
	info->mem[0].addr = (phys_addr_t)(uintptr_t)udev->mb_addr;
	info->mem[0].size = udev->ring_size = udev->data_size + CMDR_SIZE;
	info->mem[0].memtype = UIO_MEM_NONE;

	info->irqcontrol = tcmu_irqcontrol;
	info->irq = UIO_IRQ_CUSTOM;

	info->mmap = tcmu_mmap;
	info->open = tcmu_open;
	info->release = tcmu_release;

	ret = uio_register_device(tcmu_root_device, info);
	if (ret)
		goto err_register;

	/* User can set hw_block_size before enable the device */
	if (dev->dev_attrib.hw_block_size == 0)
		dev->dev_attrib.hw_block_size = 512;
	/* Other attributes can be configured in userspace */
	if (!dev->dev_attrib.hw_max_sectors)
		dev->dev_attrib.hw_max_sectors = 128;
	if (!dev->dev_attrib.emulate_write_cache)
		dev->dev_attrib.emulate_write_cache = 0;
	dev->dev_attrib.hw_queue_depth = 128;

	/* If user didn't explicitly disable netlink reply support, use
	 * module scope setting.
	 */
	if (udev->nl_reply_supported >= 0)
		udev->nl_reply_supported = tcmu_kern_cmd_reply_supported;

	/*
	 * Get a ref incase userspace does a close on the uio device before
	 * LIO has initiated tcmu_free_device.
	 */
	kref_get(&udev->kref);

	ret = tcmu_send_dev_add_event(udev);
	if (ret)
		goto err_netlink;

	mutex_lock(&root_udev_mutex);
	list_add(&udev->node, &root_udev);
	mutex_unlock(&root_udev_mutex);

	return 0;

err_netlink:
	kref_put(&udev->kref, tcmu_dev_kref_release);
	uio_unregister_device(&udev->uio_info);
err_register:
	vfree(udev->mb_addr);
	udev->mb_addr = NULL;
err_vzalloc:
	kfree(udev->data_bitmap);
	udev->data_bitmap = NULL;
err_bitmap_alloc:
	kfree(info->name);
	info->name = NULL;

	return ret;
}

static bool tcmu_dev_configured(struct tcmu_dev *udev)
{
	return udev->uio_info.uio_dev ? true : false;
}

static void tcmu_free_device(struct se_device *dev)
{
	struct tcmu_dev *udev = TCMU_DEV(dev);

	/* release ref from init */
	kref_put(&udev->kref, tcmu_dev_kref_release);
}

static void tcmu_destroy_device(struct se_device *dev)
{
	struct tcmu_dev *udev = TCMU_DEV(dev);

	del_timer_sync(&udev->cmd_timer);
	del_timer_sync(&udev->qfull_timer);

	mutex_lock(&root_udev_mutex);
	list_del(&udev->node);
	mutex_unlock(&root_udev_mutex);

	tcmu_send_dev_remove_event(udev);

	uio_unregister_device(&udev->uio_info);

	/* release ref from configure */
	kref_put(&udev->kref, tcmu_dev_kref_release);
}

static void tcmu_unblock_dev(struct tcmu_dev *udev)
{
	mutex_lock(&udev->cmdr_lock);
	clear_bit(TCMU_DEV_BIT_BLOCKED, &udev->flags);
	mutex_unlock(&udev->cmdr_lock);
}

static void tcmu_block_dev(struct tcmu_dev *udev)
{
	mutex_lock(&udev->cmdr_lock);

	if (test_and_set_bit(TCMU_DEV_BIT_BLOCKED, &udev->flags))
		goto unlock;

	/* complete IO that has executed successfully */
	tcmu_handle_completions(udev);
	/* fail IO waiting to be queued */
	run_cmdr_queue(udev, true);

unlock:
	mutex_unlock(&udev->cmdr_lock);
}

static void tcmu_reset_ring(struct tcmu_dev *udev, u8 err_level)
{
	struct tcmu_mailbox *mb;
	struct tcmu_cmd *cmd;
	int i;

	mutex_lock(&udev->cmdr_lock);

	idr_for_each_entry(&udev->commands, cmd, i) {
		if (!list_empty(&cmd->cmdr_queue_entry))
			continue;

		pr_debug("removing cmd %u on dev %s from ring (is expired %d)\n",
			  cmd->cmd_id, udev->name,
			  test_bit(TCMU_CMD_BIT_EXPIRED, &cmd->flags));

		idr_remove(&udev->commands, i);
		if (!test_bit(TCMU_CMD_BIT_EXPIRED, &cmd->flags)) {
			if (err_level == 1) {
				/*
				 * Userspace was not able to start the
				 * command or it is retryable.
				 */
				target_complete_cmd(cmd->se_cmd, SAM_STAT_BUSY);
			} else {
				/* hard failure */
				target_complete_cmd(cmd->se_cmd,
						    SAM_STAT_CHECK_CONDITION);
			}
		}
		tcmu_cmd_free_data(cmd, cmd->dbi_cnt);
		tcmu_free_cmd(cmd);
	}

	mb = udev->mb_addr;
	tcmu_flush_dcache_range(mb, sizeof(*mb));
	pr_debug("mb last %u head %u tail %u\n", udev->cmdr_last_cleaned,
		 mb->cmd_tail, mb->cmd_head);

	udev->cmdr_last_cleaned = 0;
	mb->cmd_tail = 0;
	mb->cmd_head = 0;
	tcmu_flush_dcache_range(mb, sizeof(*mb));

	del_timer(&udev->cmd_timer);

	mutex_unlock(&udev->cmdr_lock);
}

enum {
	Opt_dev_config, Opt_dev_size, Opt_hw_block_size, Opt_hw_max_sectors,
	Opt_nl_reply_supported, Opt_max_data_area_mb, Opt_err,
};

static match_table_t tokens = {
	{Opt_dev_config, "dev_config=%s"},
	{Opt_dev_size, "dev_size=%u"},
	{Opt_hw_block_size, "hw_block_size=%u"},
	{Opt_hw_max_sectors, "hw_max_sectors=%u"},
	{Opt_nl_reply_supported, "nl_reply_supported=%d"},
	{Opt_max_data_area_mb, "max_data_area_mb=%u"},
	{Opt_err, NULL}
};

static int tcmu_set_dev_attrib(substring_t *arg, u32 *dev_attrib)
{
	unsigned long tmp_ul;
	char *arg_p;
	int ret;

	arg_p = match_strdup(arg);
	if (!arg_p)
		return -ENOMEM;

	ret = kstrtoul(arg_p, 0, &tmp_ul);
	kfree(arg_p);
	if (ret < 0) {
		pr_err("kstrtoul() failed for dev attrib\n");
		return ret;
	}
	if (!tmp_ul) {
		pr_err("dev attrib must be nonzero\n");
		return -EINVAL;
	}
	*dev_attrib = tmp_ul;
	return 0;
}

static ssize_t tcmu_set_configfs_dev_params(struct se_device *dev,
		const char *page, ssize_t count)
{
	struct tcmu_dev *udev = TCMU_DEV(dev);
	char *orig, *ptr, *opts, *arg_p;
	substring_t args[MAX_OPT_ARGS];
	int ret = 0, token, tmpval;

	opts = kstrdup(page, GFP_KERNEL);
	if (!opts)
		return -ENOMEM;

	orig = opts;

	while ((ptr = strsep(&opts, ",\n")) != NULL) {
		if (!*ptr)
			continue;

		token = match_token(ptr, tokens, args);
		switch (token) {
		case Opt_dev_config:
			if (match_strlcpy(udev->dev_config, &args[0],
					  TCMU_CONFIG_LEN) == 0) {
				ret = -EINVAL;
				break;
			}
			pr_debug("TCMU: Referencing Path: %s\n", udev->dev_config);
			break;
		case Opt_dev_size:
			arg_p = match_strdup(&args[0]);
			if (!arg_p) {
				ret = -ENOMEM;
				break;
			}
			ret = kstrtoul(arg_p, 0, (unsigned long *) &udev->dev_size);
			kfree(arg_p);
			if (ret < 0)
				pr_err("kstrtoul() failed for dev_size=\n");
			break;
		case Opt_hw_block_size:
			ret = tcmu_set_dev_attrib(&args[0],
					&(dev->dev_attrib.hw_block_size));
			break;
		case Opt_hw_max_sectors:
			ret = tcmu_set_dev_attrib(&args[0],
					&(dev->dev_attrib.hw_max_sectors));
			break;
		case Opt_nl_reply_supported:
			arg_p = match_strdup(&args[0]);
			if (!arg_p) {
				ret = -ENOMEM;
				break;
			}
			ret = kstrtoint(arg_p, 0, &udev->nl_reply_supported);
			kfree(arg_p);
			if (ret < 0)
				pr_err("kstrtoint() failed for nl_reply_supported=\n");
			break;
		case Opt_max_data_area_mb:
			if (dev->export_count) {
				pr_err("Unable to set max_data_area_mb while exports exist\n");
				ret = -EINVAL;
				break;
			}

			arg_p = match_strdup(&args[0]);
			if (!arg_p) {
				ret = -ENOMEM;
				break;
			}
			ret = kstrtoint(arg_p, 0, &tmpval);
			kfree(arg_p);
			if (ret < 0) {
				pr_err("kstrtoint() failed for max_data_area_mb=\n");
				break;
			}

			if (tmpval <= 0) {
				pr_err("Invalid max_data_area %d\n", tmpval);
				ret = -EINVAL;
				break;
			}

			udev->max_blocks = TCMU_MBS_TO_BLOCKS(tmpval);
			if (udev->max_blocks > tcmu_global_max_blocks) {
				pr_err("%d is too large. Adjusting max_data_area_mb to global limit of %u\n",
				       tmpval,
				       TCMU_BLOCKS_TO_MBS(tcmu_global_max_blocks));
				udev->max_blocks = tcmu_global_max_blocks;
			}
			break;
		default:
			break;
		}

		if (ret)
			break;
	}

	kfree(orig);
	return (!ret) ? count : ret;
}

static ssize_t tcmu_show_configfs_dev_params(struct se_device *dev, char *b)
{
	struct tcmu_dev *udev = TCMU_DEV(dev);
	ssize_t bl = 0;

	bl = sprintf(b + bl, "Config: %s ",
		     udev->dev_config[0] ? udev->dev_config : "NULL");
	bl += sprintf(b + bl, "Size: %zu ", udev->dev_size);
	bl += sprintf(b + bl, "MaxDataAreaMB: %u\n",
		      TCMU_BLOCKS_TO_MBS(udev->max_blocks));

	return bl;
}

static sector_t tcmu_get_blocks(struct se_device *dev)
{
	struct tcmu_dev *udev = TCMU_DEV(dev);

	return div_u64(udev->dev_size - dev->dev_attrib.block_size,
		       dev->dev_attrib.block_size);
}

static sense_reason_t
tcmu_parse_cdb(struct se_cmd *cmd)
{
	return passthrough_parse_cdb(cmd, tcmu_queue_cmd);
}

static ssize_t tcmu_cmd_time_out_show(struct config_item *item, char *page)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
					struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);

	return snprintf(page, PAGE_SIZE, "%lu\n", udev->cmd_time_out / MSEC_PER_SEC);
}

static ssize_t tcmu_cmd_time_out_store(struct config_item *item, const char *page,
				       size_t count)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
					struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = container_of(da->da_dev,
					struct tcmu_dev, se_dev);
	u32 val;
	int ret;

	if (da->da_dev->export_count) {
		pr_err("Unable to set tcmu cmd_time_out while exports exist\n");
		return -EINVAL;
	}

	ret = kstrtou32(page, 0, &val);
	if (ret < 0)
		return ret;

	udev->cmd_time_out = val * MSEC_PER_SEC;
	return count;
}
CONFIGFS_ATTR(tcmu_, cmd_time_out);

static ssize_t tcmu_qfull_time_out_show(struct config_item *item, char *page)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
						struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);

	return snprintf(page, PAGE_SIZE, "%ld\n", udev->qfull_time_out <= 0 ?
			udev->qfull_time_out :
			udev->qfull_time_out / MSEC_PER_SEC);
}

static ssize_t tcmu_qfull_time_out_store(struct config_item *item,
					 const char *page, size_t count)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
					struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);
	s32 val;
	int ret;

	ret = kstrtos32(page, 0, &val);
	if (ret < 0)
		return ret;

	if (val >= 0) {
		udev->qfull_time_out = val * MSEC_PER_SEC;
	} else if (val == -1) {
		udev->qfull_time_out = val;
	} else {
		printk(KERN_ERR "Invalid qfull timeout value %d\n", val);
		return -EINVAL;
	}
	return count;
}
CONFIGFS_ATTR(tcmu_, qfull_time_out);

static ssize_t tcmu_max_data_area_mb_show(struct config_item *item, char *page)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
						struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);

	return snprintf(page, PAGE_SIZE, "%u\n",
			TCMU_BLOCKS_TO_MBS(udev->max_blocks));
}
CONFIGFS_ATTR_RO(tcmu_, max_data_area_mb);

static ssize_t tcmu_dev_config_show(struct config_item *item, char *page)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
						struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);

	return snprintf(page, PAGE_SIZE, "%s\n", udev->dev_config);
}

static int tcmu_send_dev_config_event(struct tcmu_dev *udev,
				      const char *reconfig_data)
{
	struct sk_buff *skb = NULL;
	void *msg_header = NULL;
	int ret = 0;

	ret = tcmu_netlink_event_init(udev, TCMU_CMD_RECONFIG_DEVICE,
				      &skb, &msg_header);
	if (ret < 0)
		return ret;
	ret = nla_put_string(skb, TCMU_ATTR_DEV_CFG, reconfig_data);
	if (ret < 0) {
		nlmsg_free(skb);
		return ret;
	}
	return tcmu_netlink_event_send(udev, TCMU_CMD_RECONFIG_DEVICE,
				       &skb, &msg_header);
}


static ssize_t tcmu_dev_config_store(struct config_item *item, const char *page,
				     size_t count)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
						struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);
	int ret, len;

	len = strlen(page);
	if (!len || len > TCMU_CONFIG_LEN - 1)
		return -EINVAL;

	/* Check if device has been configured before */
	if (tcmu_dev_configured(udev)) {
		ret = tcmu_send_dev_config_event(udev, page);
		if (ret) {
			pr_err("Unable to reconfigure device\n");
			return ret;
		}
		strlcpy(udev->dev_config, page, TCMU_CONFIG_LEN);

		ret = tcmu_update_uio_info(udev);
		if (ret)
			return ret;
		return count;
	}
	strlcpy(udev->dev_config, page, TCMU_CONFIG_LEN);

	return count;
}
CONFIGFS_ATTR(tcmu_, dev_config);

static ssize_t tcmu_dev_size_show(struct config_item *item, char *page)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
						struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);

	return snprintf(page, PAGE_SIZE, "%zu\n", udev->dev_size);
}

static int tcmu_send_dev_size_event(struct tcmu_dev *udev, u64 size)
{
	struct sk_buff *skb = NULL;
	void *msg_header = NULL;
	int ret = 0;

	ret = tcmu_netlink_event_init(udev, TCMU_CMD_RECONFIG_DEVICE,
				      &skb, &msg_header);
	if (ret < 0)
		return ret;
	ret = nla_put_u64_64bit(skb, TCMU_ATTR_DEV_SIZE,
				size, TCMU_ATTR_PAD);
	if (ret < 0) {
		nlmsg_free(skb);
		return ret;
	}
	return tcmu_netlink_event_send(udev, TCMU_CMD_RECONFIG_DEVICE,
				       &skb, &msg_header);
}

static ssize_t tcmu_dev_size_store(struct config_item *item, const char *page,
				   size_t count)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
						struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);
	u64 val;
	int ret;

	ret = kstrtou64(page, 0, &val);
	if (ret < 0)
		return ret;

	/* Check if device has been configured before */
	if (tcmu_dev_configured(udev)) {
		ret = tcmu_send_dev_size_event(udev, val);
		if (ret) {
			pr_err("Unable to reconfigure device\n");
			return ret;
		}
	}
	udev->dev_size = val;
	return count;
}
CONFIGFS_ATTR(tcmu_, dev_size);

static ssize_t tcmu_nl_reply_supported_show(struct config_item *item,
		char *page)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
						struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);

	return snprintf(page, PAGE_SIZE, "%d\n", udev->nl_reply_supported);
}

static ssize_t tcmu_nl_reply_supported_store(struct config_item *item,
		const char *page, size_t count)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
						struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);
	s8 val;
	int ret;

	ret = kstrtos8(page, 0, &val);
	if (ret < 0)
		return ret;

	udev->nl_reply_supported = val;
	return count;
}
CONFIGFS_ATTR(tcmu_, nl_reply_supported);

static ssize_t tcmu_emulate_write_cache_show(struct config_item *item,
					     char *page)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
					struct se_dev_attrib, da_group);

	return snprintf(page, PAGE_SIZE, "%i\n", da->emulate_write_cache);
}

static int tcmu_send_emulate_write_cache(struct tcmu_dev *udev, u8 val)
{
	struct sk_buff *skb = NULL;
	void *msg_header = NULL;
	int ret = 0;

	ret = tcmu_netlink_event_init(udev, TCMU_CMD_RECONFIG_DEVICE,
				      &skb, &msg_header);
	if (ret < 0)
		return ret;
	ret = nla_put_u8(skb, TCMU_ATTR_WRITECACHE, val);
	if (ret < 0) {
		nlmsg_free(skb);
		return ret;
	}
	return tcmu_netlink_event_send(udev, TCMU_CMD_RECONFIG_DEVICE,
				       &skb, &msg_header);
}

static ssize_t tcmu_emulate_write_cache_store(struct config_item *item,
					      const char *page, size_t count)
{
	struct se_dev_attrib *da = container_of(to_config_group(item),
					struct se_dev_attrib, da_group);
	struct tcmu_dev *udev = TCMU_DEV(da->da_dev);
	u8 val;
	int ret;

	ret = kstrtou8(page, 0, &val);
	if (ret < 0)
		return ret;

	/* Check if device has been configured before */
	if (tcmu_dev_configured(udev)) {
		ret = tcmu_send_emulate_write_cache(udev, val);
		if (ret) {
			pr_err("Unable to reconfigure device\n");
			return ret;
		}
	}

	da->emulate_write_cache = val;
	return count;
}
CONFIGFS_ATTR(tcmu_, emulate_write_cache);

static ssize_t tcmu_block_dev_show(struct config_item *item, char *page)
{
	struct se_device *se_dev = container_of(to_config_group(item),
						struct se_device,
						dev_action_group);
	struct tcmu_dev *udev = TCMU_DEV(se_dev);

	if (test_bit(TCMU_DEV_BIT_BLOCKED, &udev->flags))
		return snprintf(page, PAGE_SIZE, "%s\n", "blocked");
	else
		return snprintf(page, PAGE_SIZE, "%s\n", "unblocked");
}

static ssize_t tcmu_block_dev_store(struct config_item *item, const char *page,
				    size_t count)
{
	struct se_device *se_dev = container_of(to_config_group(item),
						struct se_device,
						dev_action_group);
	struct tcmu_dev *udev = TCMU_DEV(se_dev);
	u8 val;
	int ret;

	ret = kstrtou8(page, 0, &val);
	if (ret < 0)
		return ret;

	if (val > 1) {
		pr_err("Invalid block value %d\n", val);
		return -EINVAL;
	}

	if (!val)
		tcmu_unblock_dev(udev);
	else
		tcmu_block_dev(udev);
	return count;
}
CONFIGFS_ATTR(tcmu_, block_dev);

static ssize_t tcmu_reset_ring_store(struct config_item *item, const char *page,
				     size_t count)
{
	struct se_device *se_dev = container_of(to_config_group(item),
						struct se_device,
						dev_action_group);
	struct tcmu_dev *udev = TCMU_DEV(se_dev);
	u8 val;
	int ret;

	ret = kstrtou8(page, 0, &val);
	if (ret < 0)
		return ret;

	if (val != 1 && val != 2) {
		pr_err("Invalid reset ring value %d\n", val);
		return -EINVAL;
	}

	tcmu_reset_ring(udev, val);
	return count;
}
CONFIGFS_ATTR_WO(tcmu_, reset_ring);

static struct configfs_attribute *tcmu_attrib_attrs[] = {
	&tcmu_attr_cmd_time_out,
	&tcmu_attr_qfull_time_out,
	&tcmu_attr_max_data_area_mb,
	&tcmu_attr_dev_config,
	&tcmu_attr_dev_size,
	&tcmu_attr_emulate_write_cache,
	&tcmu_attr_nl_reply_supported,
	NULL,
};

static struct configfs_attribute **tcmu_attrs;

static struct configfs_attribute *tcmu_action_attrs[] = {
	&tcmu_attr_block_dev,
	&tcmu_attr_reset_ring,
	NULL,
};

static struct target_backend_ops tcmu_ops = {
	.name			= "user",
	.owner			= THIS_MODULE,
	.transport_flags	= TRANSPORT_FLAG_PASSTHROUGH,
	.attach_hba		= tcmu_attach_hba,
	.detach_hba		= tcmu_detach_hba,
	.alloc_device		= tcmu_alloc_device,
	.configure_device	= tcmu_configure_device,
	.destroy_device		= tcmu_destroy_device,
	.free_device		= tcmu_free_device,
	.parse_cdb		= tcmu_parse_cdb,
	.set_configfs_dev_params = tcmu_set_configfs_dev_params,
	.show_configfs_dev_params = tcmu_show_configfs_dev_params,
	.get_device_type	= sbc_get_device_type,
	.get_blocks		= tcmu_get_blocks,
	.tb_dev_action_attrs	= tcmu_action_attrs,
};

static void find_free_blocks(void)
{
	struct tcmu_dev *udev;
	loff_t off;
	u32 start, end, block, total_freed = 0;

	if (atomic_read(&global_db_count) <= tcmu_global_max_blocks)
		return;

	mutex_lock(&root_udev_mutex);
	list_for_each_entry(udev, &root_udev, node) {
		mutex_lock(&udev->cmdr_lock);

		/* Try to complete the finished commands first */
		tcmu_handle_completions(udev);

		/* Skip the udevs in idle */
		if (!udev->dbi_thresh) {
			mutex_unlock(&udev->cmdr_lock);
			continue;
		}

		end = udev->dbi_max + 1;
		block = find_last_bit(udev->data_bitmap, end);
		if (block == udev->dbi_max) {
			/*
			 * The last bit is dbi_max, so it is not possible
			 * reclaim any blocks.
			 */
			mutex_unlock(&udev->cmdr_lock);
			continue;
		} else if (block == end) {
			/* The current udev will goto idle state */
			udev->dbi_thresh = start = 0;
			udev->dbi_max = 0;
		} else {
			udev->dbi_thresh = start = block + 1;
			udev->dbi_max = block;
		}

		/* Here will truncate the data area from off */
		off = udev->data_off + start * DATA_BLOCK_SIZE;
		unmap_mapping_range(udev->inode->i_mapping, off, 0, 1);

		/* Release the block pages */
		tcmu_blocks_release(&udev->data_blocks, start, end);
		mutex_unlock(&udev->cmdr_lock);

		total_freed += end - start;
		pr_debug("Freed %u blocks (total %u) from %s.\n", end - start,
			 total_freed, udev->name);
	}
	mutex_unlock(&root_udev_mutex);

	if (atomic_read(&global_db_count) > tcmu_global_max_blocks)
		schedule_delayed_work(&tcmu_unmap_work, msecs_to_jiffies(5000));
}

static void check_timedout_devices(void)
{
	struct tcmu_dev *udev, *tmp_dev;
	LIST_HEAD(devs);

	spin_lock_bh(&timed_out_udevs_lock);
	list_splice_init(&timed_out_udevs, &devs);

	list_for_each_entry_safe(udev, tmp_dev, &devs, timedout_entry) {
		list_del_init(&udev->timedout_entry);
		spin_unlock_bh(&timed_out_udevs_lock);

		mutex_lock(&udev->cmdr_lock);
		idr_for_each(&udev->commands, tcmu_check_expired_cmd, NULL);
		mutex_unlock(&udev->cmdr_lock);

		spin_lock_bh(&timed_out_udevs_lock);
	}

	spin_unlock_bh(&timed_out_udevs_lock);
}

static void tcmu_unmap_work_fn(struct work_struct *work)
{
	check_timedout_devices();
	find_free_blocks();
}

static int __init tcmu_module_init(void)
{
	int ret, i, k, len = 0;

	BUILD_BUG_ON((sizeof(struct tcmu_cmd_entry) % TCMU_OP_ALIGN_SIZE) != 0);

	INIT_DELAYED_WORK(&tcmu_unmap_work, tcmu_unmap_work_fn);

	tcmu_cmd_cache = kmem_cache_create("tcmu_cmd_cache",
				sizeof(struct tcmu_cmd),
				__alignof__(struct tcmu_cmd),
				0, NULL);
	if (!tcmu_cmd_cache)
		return -ENOMEM;

	tcmu_root_device = root_device_register("tcm_user");
	if (IS_ERR(tcmu_root_device)) {
		ret = PTR_ERR(tcmu_root_device);
		goto out_free_cache;
	}

	ret = genl_register_family(&tcmu_genl_family);
	if (ret < 0) {
		goto out_unreg_device;
	}

	for (i = 0; passthrough_attrib_attrs[i] != NULL; i++) {
		len += sizeof(struct configfs_attribute *);
	}
	for (i = 0; tcmu_attrib_attrs[i] != NULL; i++) {
		len += sizeof(struct configfs_attribute *);
	}
	len += sizeof(struct configfs_attribute *);

	tcmu_attrs = kzalloc(len, GFP_KERNEL);
	if (!tcmu_attrs) {
		ret = -ENOMEM;
		goto out_unreg_genl;
	}

	for (i = 0; passthrough_attrib_attrs[i] != NULL; i++) {
		tcmu_attrs[i] = passthrough_attrib_attrs[i];
	}
	for (k = 0; tcmu_attrib_attrs[k] != NULL; k++) {
		tcmu_attrs[i] = tcmu_attrib_attrs[k];
		i++;
	}
	tcmu_ops.tb_dev_attrib_attrs = tcmu_attrs;

	ret = transport_backend_register(&tcmu_ops);
	if (ret)
		goto out_attrs;

	return 0;

out_attrs:
	kfree(tcmu_attrs);
out_unreg_genl:
	genl_unregister_family(&tcmu_genl_family);
out_unreg_device:
	root_device_unregister(tcmu_root_device);
out_free_cache:
	kmem_cache_destroy(tcmu_cmd_cache);

	return ret;
}

static void __exit tcmu_module_exit(void)
{
	cancel_delayed_work_sync(&tcmu_unmap_work);
	target_backend_unregister(&tcmu_ops);
	kfree(tcmu_attrs);
	genl_unregister_family(&tcmu_genl_family);
	root_device_unregister(tcmu_root_device);
	kmem_cache_destroy(tcmu_cmd_cache);
}

MODULE_DESCRIPTION("TCM USER subsystem plugin");
MODULE_AUTHOR("Shaohua Li <shli@kernel.org>");
MODULE_AUTHOR("Andy Grover <agrover@redhat.com>");
MODULE_LICENSE("GPL");

module_init(tcmu_module_init);
module_exit(tcmu_module_exit);
