BEGIN;

CREATE TABLE IF NOT EXISTS public.runes
(
    id SERIAL PRIMARY KEY,
    number numeric NOT NULL,
    rune_id character varying(32) NOT NULL,
    spaced_rune character varying(64) NOT NULL,
    divisibility smallint NOT NULL,
    symbol character varying(4),
    etching character varying(64) NOT NULL,
    premine numeric NOT NULL,
    terms_amount numeric,
    terms_cap numeric,
    terms_height_start numeric,
    terms_height_end numeric,
    terms_offset_start numeric,
    terms_offset_end numeric,
    mints numeric NOT NULL,
    burned numeric NOT NULL,
    block numeric NOT NULL,
    timestamp timestamp with time zone NOT NULL,
    turbo boolean NOT NULL DEFAULT FALSE,
    reorg boolean NOT NULL DEFAULT FALSE
);

CREATE TABLE IF NOT EXISTS public.rune_mints
(
    id SERIAL PRIMARY KEY,
    rune_id character varying(32) NOT NULL,
    mints numeric NOT NULL,
    block numeric NOT NULL,
    reorg boolean NOT NULL DEFAULT FALSE
);

CREATE TABLE IF NOT EXISTS public.rune_burned
(
    id SERIAL PRIMARY KEY,
    rune_id character varying(32) NOT NULL,
    burned numeric NOT NULL,
    block numeric NOT NULL,
    reorg boolean NOT NULL DEFAULT FALSE
);

CREATE TABLE IF NOT EXISTS public.transactions
(
    id SERIAL PRIMARY KEY,
    txid character varying(64) NOT NULL,
    transaction json NOT NULL,
    block numeric NOT NULL,
    reorg boolean NOT NULL DEFAULT FALSE
);

CREATE TABLE IF NOT EXISTS public.rune_balances
(
    id SERIAL PRIMARY KEY,
    rune_id character varying(32) NOT NULL,
    address character varying(64) NOT NULL,
    is_increased boolean NOT NULL,
    amount numeric NOT NULL,
    block numeric NOT NULL,
    reorg boolean NOT NULL DEFAULT FALSE
);

CREATE TABLE IF NOT EXISTS public.rune_transactions
(
    id SERIAL PRIMARY KEY,
    rune_id character varying(32) NOT NULL,
    txid character varying(64) NOT NULL,
    burn boolean NOT NULL DEFAULT FALSE,
    etch boolean NOT NULL DEFAULT FALSE,
    mint boolean NOT NULL DEFAULT FALSE,
    transfer boolean NOT NULL DEFAULT FALSE,
    block numeric NOT NULL,
    timestamp timestamp with time zone NOT NULL,
    reorg boolean NOT NULL DEFAULT FALSE
);

CREATE TABLE IF NOT EXISTS public.address_transactions
(
    id SERIAL PRIMARY KEY,
    address character varying(64) NOT NULL,
    txid character varying(64) NOT NULL,
    block numeric NOT NULL,
    reorg boolean NOT NULL DEFAULT FALSE
);

CREATE INDEX idx_runes_block ON public.runes (block);
CREATE INDEX idx_rune_mints_block ON public.rune_mints (block);
CREATE INDEX idx_rune_burned_block ON public.rune_burned (block);
CREATE INDEX idx_transactions_block ON public.transactions (block);
CREATE INDEX idx_rune_balances_block ON public.rune_balances (block);
CREATE INDEX idx_rune_transactions_block ON public.rune_transactions (block);
CREATE INDEX idx_address_transactions_block ON public.address_transactions (block);

END;
