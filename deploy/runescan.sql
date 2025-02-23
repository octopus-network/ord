BEGIN;

CREATE TABLE IF NOT EXISTS public.runes (
    id SERIAL PRIMARY KEY,
    number BIGINT NOT NULL,
    rune_id VARCHAR(32) NOT NULL,
    burned NUMERIC NOT NULL,
    divisibility SMALLINT NOT NULL,
    etching VARCHAR(64) NOT NULL,
    mints NUMERIC NOT NULL,
    premine NUMERIC NOT NULL,
    spaced_rune VARCHAR(64) NOT NULL,
    symbol VARCHAR(1),
    terms_cap NUMERIC,
    terms_height_start BIGINT,
    terms_height_end BIGINT,
    terms_amount NUMERIC,
    terms_offset_start BIGINT,
    terms_offset_end BIGINT,
    timestamp TIMESTAMP WITH TIME ZONE NOT NULL,
    turbo BOOLEAN NOT NULL,
    block BIGINT NOT NULL,
    reorg BOOLEAN NOT NULL DEFAULT FALSE
);

CREATE UNIQUE INDEX idx_runes_rune_id_reorg ON public.runes(rune_id) WHERE reorg = FALSE;
CREATE UNIQUE INDEX idx_runes_spaced_rune_reorg ON public.runes(spaced_rune) WHERE reorg = FALSE;
CREATE UNIQUE INDEX idx_runes_number_reorg ON public.runes(number) WHERE reorg = FALSE;
CREATE INDEX idx_runes_block_reorg ON public.runes(block) WHERE reorg = FALSE;

CREATE TABLE IF NOT EXISTS public.transactions
(
    id SERIAL PRIMARY KEY,
    txid VARCHAR(64) NOT NULL,
    transaction JSON NOT NULL,
    block BIGINT NOT NULL,
    reorg BOOLEAN NOT NULL DEFAULT FALSE
);

CREATE UNIQUE INDEX idx_transactions_txid_reorg ON public.transactions(txid) WHERE reorg = FALSE;
CREATE INDEX idx_transactions_block_reorg ON public.transactions(block) WHERE reorg = FALSE;


CREATE TABLE IF NOT EXISTS public.rune_transactions
(
    id SERIAL PRIMARY KEY,
    rune_id VARCHAR(32) NOT NULL,
    txid VARCHAR(64) NOT NULL,
    burn BOOLEAN NOT NULL DEFAULT FALSE,
    etch BOOLEAN NOT NULL DEFAULT FALSE,
    mint BOOLEAN NOT NULL DEFAULT FALSE,
    transfer BOOLEAN NOT NULL DEFAULT FALSE,
    timestamp TIMESTAMP WITH TIME ZONE NOT NULL,
    block BIGINT NOT NULL,
    reorg BOOLEAN NOT NULL DEFAULT FALSE
);

CREATE UNIQUE INDEX idx_rune_transactions_rune_id_txid_reorg ON public.rune_transactions(rune_id, txid) WHERE reorg = FALSE;
CREATE INDEX idx_rune_transactions_rune_id_reorg ON public.rune_transactions(rune_id) WHERE reorg = FALSE;
CREATE INDEX idx_rune_transactions_block_reorg ON public.rune_transactions(block) WHERE reorg = FALSE;

CREATE TABLE IF NOT EXISTS public.address_transactions
(
    id SERIAL PRIMARY KEY,
    address VARCHAR(64) NOT NULL,
    txid VARCHAR(64) NOT NULL,
    block BIGINT NOT NULL,
    reorg BOOLEAN NOT NULL DEFAULT FALSE
);

CREATE UNIQUE INDEX idx_address_transactions_address_txid_reorg ON public.address_transactions(address, txid) WHERE reorg = FALSE;
CREATE INDEX idx_address_transactions_address_reorg ON public.address_transactions(address) WHERE reorg = FALSE;
CREATE INDEX idx_address_transactions_block_reorg ON public.address_transactions(block) WHERE reorg = FALSE;

CREATE TABLE IF NOT EXISTS public.address_rune_balance
(
    address VARCHAR(64) NOT NULL,
    rune_id VARCHAR(32) NOT NULL,
    balance NUMERIC NOT NULL,
    PRIMARY KEY (address, rune_id)
);

CREATE TABLE IF NOT EXISTS public.updated_runes (
    id SERIAL PRIMARY KEY,
    rune_id VARCHAR(32) NOT NULL,
    block BIGINT NOT NULL,
    reorg BOOLEAN NOT NULL DEFAULT FALSE
);

CREATE INDEX idx_updated_runes_block_reorg ON public.updated_runes(block) WHERE reorg = FALSE;

CREATE TABLE IF NOT EXISTS public.updated_addresses (
    id SERIAL PRIMARY KEY,
    address VARCHAR(64) NOT NULL,
    block BIGINT NOT NULL,
    reorg BOOLEAN NOT NULL DEFAULT FALSE
);

CREATE INDEX idx_updated_addresses_block_reorg ON public.updated_addresses(block) WHERE reorg = FALSE;

END;
